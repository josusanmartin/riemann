import { timingSafeEqual } from "node:crypto";
import { getE2BApiKey, getE2BTemplate } from "@/lib/e2b-config";

export const runtime = "nodejs";
export const maxDuration = 60;

const identifierPattern = /^[A-Za-z0-9][A-Za-z0-9_-]{0,299}$/;

type TemplateSummary = {
  templateID: string;
  names?: string[];
  aliases?: string[];
  updatedAt: string;
};

type TemplateBuild = {
  buildID: string;
  createdAt: string;
};

type TemplateWithBuilds = {
  builds: TemplateBuild[];
};

type TemplateBuildLogs = {
  logs: Array<{
    timestamp: string;
    level: string;
    message: string;
  }>;
};

function noStore(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "no-store" },
  });
}

function authorized(request: Request): boolean {
  const secret = process.env.E2B_TEMPLATE_ADMIN_SECRET;
  const supplied = request.headers.get("authorization");
  if (!secret || secret.length < 32 || !supplied) return false;
  const expected = Buffer.from(`Bearer ${secret}`, "utf8");
  const actual = Buffer.from(supplied, "utf8");
  return expected.length === actual.length && timingSafeEqual(expected, actual);
}

function apiKey(): string {
  const key = getE2BApiKey();
  if (!key) throw new Error("E2B verification is not configured");
  return key;
}

async function e2bApi<T>(path: string, key: string): Promise<T> {
  const response = await fetch(new URL(path, "https://api.e2b.app"), {
    headers: { "X-API-KEY": key },
    cache: "no-store",
  });
  if (!response.ok) {
    const detail = (await response.text()).slice(0, 1_000);
    throw new Error(`E2B API ${response.status}: ${detail}`);
  }
  return (await response.json()) as T;
}

async function latestBuildCoordinates(
  name: string,
  key: string,
): Promise<{ templateId: string; buildId: string } | undefined> {
  const templates = await e2bApi<TemplateSummary[]>("/v2/templates?limit=100", key);
  const template = templates
    .filter((entry) =>
      [...(entry.names ?? []), ...(entry.aliases ?? [])].some(
        (candidate) => candidate === name || candidate.startsWith(`${name}:`),
      ),
    )
    .sort((left, right) => left.updatedAt.localeCompare(right.updatedAt))
    .at(-1);
  if (!template || !identifierPattern.test(template.templateID)) return undefined;

  const details = await e2bApi<TemplateWithBuilds>(
    `/templates/${encodeURIComponent(template.templateID)}?limit=100`,
    key,
  );
  const build = details.builds
    .sort((left, right) => left.createdAt.localeCompare(right.createdAt))
    .at(-1);
  if (!build || !identifierPattern.test(build.buildID)) return undefined;
  return { templateId: template.templateID, buildId: build.buildID };
}

export async function POST(request: Request): Promise<Response> {
  if (!authorized(request)) return noStore(401, { error: "unauthorized" });

  try {
    const key = apiKey();
    const name = getE2BTemplate();
    const force = new URL(request.url).searchParams.get("force") === "1";
    const { Template } = await import("e2b");
    if (!force && (await Template.exists(name, { apiKey: key }))) {
      return noStore(200, { status: "ready", name });
    }

    const { createRiemannVerifierTemplate } = await import(
      "../../../../../e2b/template"
    );
    const build = await Template.buildInBackground(
      createRiemannVerifierTemplate(process.cwd()),
      name,
      { apiKey: key, cpuCount: 4, memoryMB: 8_192 },
    );
    return noStore(202, {
      status: "building",
      name: build.name,
      templateId: build.templateId,
      buildId: build.buildId,
      tags: build.tags,
    });
  } catch (error) {
    console.error("Unable to start E2B verifier template build", error);
    return noStore(502, {
      error: "template_build_start_failed",
      message: error instanceof Error ? error.message : "E2B template build failed",
    });
  }
}

export async function GET(request: Request): Promise<Response> {
  if (!authorized(request)) return noStore(401, { error: "unauthorized" });

  try {
    const key = apiKey();
    const url = new URL(request.url);
    let templateId = url.searchParams.get("templateId");
    let buildId = url.searchParams.get("buildId");
    const { Template } = await import("e2b");
    if (url.searchParams.get("latest") === "1") {
      const latest = await latestBuildCoordinates(getE2BTemplate(), key);
      if (!latest) {
        return noStore(404, { error: "template_build_not_found" });
      }
      templateId = latest.templateId;
      buildId = latest.buildId;
    }
    if (!templateId && !buildId) {
      const name = getE2BTemplate();
      return noStore(200, {
        status: (await Template.exists(name, { apiKey: key }))
          ? "ready"
          : "missing",
        name,
      });
    }
    if (
      !templateId ||
      !buildId ||
      !identifierPattern.test(templateId) ||
      !identifierPattern.test(buildId)
    ) {
      return noStore(400, { error: "invalid_build_coordinates" });
    }

    const build = await Template.getBuildStatus(
      { templateId, buildId },
      { apiKey: key },
    );
    const buildLogs = await e2bApi<TemplateBuildLogs>(
      `/templates/${encodeURIComponent(templateId)}/builds/${encodeURIComponent(buildId)}/logs?limit=200&direction=backward`,
      key,
    );
    return noStore(200, {
      status: build.status,
      templateId: build.templateID,
      buildId: build.buildID,
      reason: build.reason
        ? { message: build.reason.message, step: build.reason.step }
        : undefined,
      logs: [...buildLogs.logs]
        .sort((left, right) => left.timestamp.localeCompare(right.timestamp))
        .slice(-80)
        .map((entry) => ({
          timestamp: entry.timestamp,
          level: entry.level,
          message: entry.message.slice(0, 2_000),
        })),
    });
  } catch (error) {
    console.error("Unable to inspect E2B verifier template build", error);
    return noStore(502, {
      error: "template_build_status_failed",
      message: error instanceof Error ? error.message : "E2B template status failed",
    });
  }
}
