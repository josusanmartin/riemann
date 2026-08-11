import { timingSafeEqual } from "node:crypto";
import { getE2BApiKey, getE2BTemplate } from "@/lib/e2b-config";

export const runtime = "nodejs";
export const maxDuration = 60;

const identifierPattern = /^[A-Za-z0-9][A-Za-z0-9_-]{0,299}$/;

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
    const templateId = url.searchParams.get("templateId");
    const buildId = url.searchParams.get("buildId");
    const { Template } = await import("e2b");
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
    return noStore(200, {
      status: build.status,
      templateId: build.templateID,
      buildId: build.buildID,
      reason: build.reason
        ? { message: build.reason.message, step: build.reason.step }
        : undefined,
      logs: build.logEntries.slice(-40).map((entry) => ({
        timestamp: entry.timestamp.toISOString(),
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
