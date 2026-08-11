import { timingSafeEqual } from "node:crypto";
import { getE2BApiKey } from "@/lib/e2b-config";

export const runtime = "nodejs";
export const maxDuration = 300;

const identifierPattern = /^[A-Za-z0-9][A-Za-z0-9_-]{0,299}$/;
const TEMPLATE_BUILD_NAME = "riemann-fail-verifier";

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

async function smokeTemplate(templateReference: string, key: string) {
  const { Sandbox } = await import("e2b");
  const sandbox = await Sandbox.create({
    apiKey: key,
    template: templateReference,
    timeoutMs: 5 * 60 * 1_000,
    secure: true,
    allowInternetAccess: false,
    network: { allowPublicTraffic: false },
  });

  try {
    const info = await sandbox.getInfo();
    if (info.allowInternetAccess !== false) {
      throw new Error("E2B did not confirm outbound network isolation");
    }
    const sandboxEnv = {
      HOME: "/home/riemann",
      PATH: "/opt/riemann/tools/bin:/home/riemann/.elan/bin:/usr/local/bin:/usr/bin:/bin",
      E2B_SANDBOX: "true",
      RIEMANN_E2B_NETWORK_DISABLED: "1",
      COMPARATOR_LANDRUN: "/opt/riemann/tools/bin/landrun",
      COMPARATOR_LEAN4EXPORT: "/opt/riemann/tools/bin/lean4export",
      COMPARATOR_NANODA: "/opt/riemann/tools/bin/nanoda_bin",
    };
    await sandbox.commands.run(
      "set -euo pipefail; " +
        "install -d -o riemann -g riemann -m 0700 /home/riemann/tmp/zeta-smoke /home/riemann/tmp/bootstrap-smoke && " +
        "tar --exclude='./.lake' -C /opt/riemann/zeta23 -cf - . | tar -C /home/riemann/tmp/zeta-smoke -xf - && " +
        "install -d -o riemann -g riemann /home/riemann/tmp/zeta-smoke/.lake /home/riemann/tmp/zeta-smoke/.lake/build/lib/lean /home/riemann/tmp/zeta-smoke/.lake/build/ir && " +
        "ln -s /opt/riemann/zeta23/.lake/packages /home/riemann/tmp/zeta-smoke/.lake/packages && " +
        "for artifact_dir in lib/lean ir; do for source in /opt/riemann/zeta23/.lake/build/$artifact_dir/Zeta23 /opt/riemann/zeta23/.lake/build/$artifact_dir/Zeta23.*; do if [ -e \"$source\" ]; then ln -s \"$source\" \"/home/riemann/tmp/zeta-smoke/.lake/build/$artifact_dir/${source##*/}\"; fi; done; done && " +
        "test -s /home/riemann/tmp/zeta-smoke/.lake/build/lib/lean/Zeta23/Unconditional.olean && " +
        "cp -R /opt/riemann/challenge/smoke/. /home/riemann/tmp/bootstrap-smoke/ && " +
        "chown -R riemann:riemann /home/riemann/tmp/zeta-smoke /home/riemann/tmp/bootstrap-smoke",
      { user: "root", timeoutMs: 60_000 },
    );
    const zetaResult = await sandbox.commands.run(
      "/opt/riemann/tools/bin/lake env lean Zeta23/Unconditional.lean",
      {
        user: "riemann",
        cwd: "/home/riemann/tmp/zeta-smoke",
        timeoutMs: 4 * 60 * 1_000,
        envs: sandboxEnv,
      },
    );
    const result = await sandbox.commands.run(
      "bash /opt/riemann/scripts/run-comparator-e2b.sh /opt/riemann/tools/bin/comparator config.json",
      {
        user: "riemann",
        cwd: "/home/riemann/tmp/bootstrap-smoke",
        timeoutMs: 4 * 60 * 1_000,
        envs: sandboxEnv,
      },
    );
    return {
      sandboxId: sandbox.sandboxId,
      exitCode: result.exitCode,
      zetaElaborationExitCode: zetaResult.exitCode,
      stdout: result.stdout.slice(-4_000),
      stderr: result.stderr.slice(-4_000),
      networkIsolated: true,
    };
  } finally {
    await sandbox.kill().catch(() => undefined);
  }
}

export async function POST(request: Request): Promise<Response> {
  if (!authorized(request)) return noStore(401, { error: "unauthorized" });
  const url = new URL(request.url);
  const action = url.searchParams.get("action");

  try {
    const key = apiKey();
    if (action === "smoke") {
      const templateId = url.searchParams.get("templateId");
      const buildId = url.searchParams.get("buildId");
      if (
        !templateId ||
        !buildId ||
        !identifierPattern.test(templateId) ||
        !identifierPattern.test(buildId)
      ) {
        return noStore(400, { error: "invalid_template_build_coordinates" });
      }
      const { Template } = await import("e2b");
      const build = await Template.getBuildStatus(
        { templateId, buildId },
        { apiKey: key },
      );
      if (build.status !== "ready") {
        return noStore(409, { error: "template_build_not_ready" });
      }
      const templateReference = `${TEMPLATE_BUILD_NAME}:${buildId}`;
      return noStore(200, {
        status: "passed",
        templateId,
        buildId,
        templateReference,
        smoke: await smokeTemplate(templateReference, key),
      });
    }
    const name = TEMPLATE_BUILD_NAME;
    const force = url.searchParams.get("force") === "1";
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
    const smoke = action === "smoke";
    console.error(
      smoke
        ? "E2B verifier template smoke test failed"
        : "Unable to start E2B verifier template build",
      error,
    );
    return noStore(502, {
      error: smoke ? "template_smoke_failed" : "template_build_start_failed",
      message:
        error instanceof Error
          ? error.message
          : smoke
            ? "E2B template smoke test failed"
            : "E2B template build failed",
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
    const rawLogsOffset = url.searchParams.get("logsOffset");
    if (rawLogsOffset && !/^\d{1,7}$/.test(rawLogsOffset)) {
      return noStore(400, { error: "invalid_logs_offset" });
    }
    const logsOffset = rawLogsOffset ? Number(rawLogsOffset) : undefined;
    const { Template } = await import("e2b");
    if (url.searchParams.get("latest") === "1") {
      const latest = await latestBuildCoordinates(TEMPLATE_BUILD_NAME, key);
      if (!latest) {
        return noStore(404, { error: "template_build_not_found" });
      }
      templateId = latest.templateId;
      buildId = latest.buildId;
    }
    if (!templateId && !buildId) {
      const name = TEMPLATE_BUILD_NAME;
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
      { apiKey: key, logsOffset },
    );
    const buildLogs =
      build.status === "error" && logsOffset === undefined
        ? await e2bApi<TemplateBuildLogs>(
            `/templates/${encodeURIComponent(templateId)}/builds/${encodeURIComponent(buildId)}/logs?limit=100&direction=backward`,
            key,
          )
        : {
            logs: build.logEntries.map((entry) => ({
              timestamp: entry.timestamp.toISOString(),
              level: entry.level,
              message: entry.message,
            })),
          };
    return noStore(200, {
      status: build.status,
      templateId: build.templateID,
      buildId: build.buildID,
      reason: build.reason
        ? {
            message: build.reason.message,
            step: build.reason.step,
            logs: build.reason.logEntries.map((entry) => ({
              timestamp: entry.timestamp.toISOString(),
              level: entry.level,
              message: entry.message.slice(0, 2_000),
            })),
          }
        : undefined,
      logsOffset: logsOffset ?? 0,
      nextLogsOffset: (logsOffset ?? 0) + build.logEntries.length,
      logs: [...buildLogs.logs]
        .sort((left, right) => left.timestamp.localeCompare(right.timestamp))
        .slice(logsOffset === undefined ? -80 : 0)
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
