import { timingSafeEqual } from "node:crypto";
import type { Sandbox as E2BSandbox } from "e2b";
import { getE2BApiKey } from "@/lib/e2b-config";

export const runtime = "nodejs";
export const maxDuration = 300;

const identifierPattern = /^[A-Za-z0-9][A-Za-z0-9_-]{0,299}$/;
const TEMPLATE_BUILD_NAME = "riemann-fail-verifier";
const EXTENDED_SMOKE_ROOT = "/home/riemann/tmp/extended-smoke";
const EXTENDED_SMOKE_SCRIPT = `#!/usr/bin/env bash
set -uo pipefail

root="${EXTENDED_SMOKE_ROOT}"
printf 'zeta-runtime-import\n' > "$root/state"
zeta_started=$(date +%s)
cd /home/riemann/tmp/zeta-smoke || exit 2
/opt/riemann/tools/bin/lake env lean ZetaRuntimeProbe.lean \
  > "$root/zeta.log" 2>&1
zeta_status=$?
printf '%s\n' "$zeta_status" > "$root/zeta.status"
printf '%s\n' "$(( $(date +%s) - zeta_started ))" > "$root/zeta.seconds"

if [[ "$zeta_status" -eq 0 ]]; then
  printf 'comparator-nanoda\n' > "$root/state"
  comparator_started=$(date +%s)
  cd /home/riemann/tmp/bootstrap-smoke || exit 2
  bash /opt/riemann/scripts/run-comparator-e2b.sh \
    /opt/riemann/tools/bin/comparator config.json \
    > "$root/comparator.log" 2>&1
  comparator_status=$?
  printf '%s\n' "$comparator_status" > "$root/comparator.status"
  printf '%s\n' "$(( $(date +%s) - comparator_started ))" \
    > "$root/comparator.seconds"
else
  printf '125\n' > "$root/comparator.status"
  printf '0\n' > "$root/comparator.seconds"
  printf 'Skipped because the Zeta runtime import failed.\n' \
    > "$root/comparator.log"
fi

printf 'done\n' > "$root/state"
`;

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

function commandFailure(error: unknown): {
  exitCode: number;
  stdout: string;
  stderr: string;
} {
  const detail =
    typeof error === "object" && error !== null
      ? (error as Record<string, unknown>)
      : {};
  return {
    exitCode: typeof detail.exitCode === "number" ? detail.exitCode : 124,
    stdout: typeof detail.stdout === "string" ? detail.stdout.slice(-4_000) : "",
    stderr:
      typeof detail.stderr === "string"
        ? detail.stderr.slice(-4_000)
        : error instanceof Error
          ? error.message.slice(-4_000)
          : "The E2B command did not complete",
  };
}

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
    timeoutMs: 8 * 60 * 1_000,
    secure: true,
    allowInternetAccess: false,
    network: {
      allowPublicTraffic: false,
      denyOut: ["0.0.0.0/0"],
    },
  });

  try {
    const info = await sandbox.getInfo();
    if (
      info.allowInternetAccess !== false ||
      !info.network?.denyOut?.includes("0.0.0.0/0")
    ) {
      throw new Error("E2B did not confirm the deny-all outbound rule");
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
    const diagnosticsResult = await sandbox.commands.run(
      "set -uo pipefail; " +
        "printf 'git_version='; git --version; " +
        "printf 'lake='; test -x /opt/riemann/tools/bin/lake && echo present || echo missing; " +
        "printf 'mathlib_git='; test -d /opt/riemann/zeta23/.lake/packages/mathlib/.git && echo present || echo missing; " +
        "printf 'mathlib_remote='; git -C /opt/riemann/zeta23/.lake/packages/mathlib config --get remote.origin.url 2>/dev/null || echo unavailable; " +
        "printf 'mathlib_unprivileged_remote='; runuser -u riemann -- git -C /opt/riemann/zeta23/.lake/packages/mathlib remote get-url origin 2>/dev/null || echo unavailable; " +
        "printf 'mathlib_head='; git -C /opt/riemann/zeta23/.lake/packages/mathlib rev-parse HEAD 2>/dev/null || echo unavailable; " +
        "printf 'mathlib_olean_mode='; stat -c '%U:%G %a' /opt/riemann/zeta23/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/CStarAlgebra/Classes.olean 2>/dev/null || echo unavailable; " +
        "printf 'mathlib_olean_unprivileged='; runuser -u riemann -- test -r /opt/riemann/zeta23/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/CStarAlgebra/Classes.olean && echo readable || echo unreadable; " +
        "printf 'lean_mode='; stat -c '%U:%G %a' /home/riemann/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean 2>/dev/null || echo unavailable; " +
        "printf 'safe_directory_count='; git config --system --get-all safe.directory 2>/dev/null | wc -l; " +
        "printf 'tls_egress='; python3 -c 'import socket, ssl; raw = socket.create_connection((\"1.1.1.1\", 443), 3); tls = ssl.create_default_context().wrap_socket(raw, server_hostname=\"one.one.one.one\"); tls.sendall(b\"HEAD / HTTP/1.0\\r\\nHost: one.one.one.one\\r\\n\\r\\n\"); tls.settimeout(3); assert tls.recv(1)' >/dev/null 2>&1 && echo reachable || echo blocked; " +
        "printf 'http_egress='; python3 -c 'import socket; stream = socket.create_connection((\"1.1.1.1\", 80), 3); stream.sendall(b\"HEAD / HTTP/1.0\\r\\nHost: one.one.one.one\\r\\n\\r\\n\"); stream.settimeout(3); assert stream.recv(1)' >/dev/null 2>&1 && echo reachable || echo blocked; " +
        "printf 'manifest_url='; jq -r '.packages[] | select(.name == \"mathlib\") | .url' /opt/riemann/zeta23/lake-manifest.json",
      { user: "root", timeoutMs: 30_000 },
    );
    await sandbox.commands.run(
      "set -euo pipefail; " +
        "install -d -o riemann -g riemann -m 0700 /home/riemann/tmp/zeta-smoke /home/riemann/tmp/bootstrap-smoke && " +
        "tar --exclude='./.lake' -C /opt/riemann/zeta23 -cf - . | tar -C /home/riemann/tmp/zeta-smoke -xf - && " +
        "install -d -o riemann -g riemann /home/riemann/tmp/zeta-smoke/.lake /home/riemann/tmp/zeta-smoke/.lake/build/lib/lean /home/riemann/tmp/zeta-smoke/.lake/build/ir && " +
        "ln -s /opt/riemann/zeta23/.lake/packages /home/riemann/tmp/zeta-smoke/.lake/packages && " +
        "for artifact_dir in lib/lean ir; do for source in /opt/riemann/zeta23/.lake/build/$artifact_dir/Zeta23 /opt/riemann/zeta23/.lake/build/$artifact_dir/Zeta23.*; do if [ -e \"$source\" ]; then ln -s \"$source\" \"/home/riemann/tmp/zeta-smoke/.lake/build/$artifact_dir/${source##*/}\"; fi; done; done && " +
        "test -s /home/riemann/tmp/zeta-smoke/.lake/build/lib/lean/Zeta23/Unconditional.olean && " +
        "printf '%s\\n' 'import Zeta23.Unconditional' '#check Zeta23.two_thirds_on_critical_line' '#check Zeta23.two_thirds_on_critical_line_cumulative' > /home/riemann/tmp/zeta-smoke/ZetaRuntimeProbe.lean && " +
        "cp -R /opt/riemann/challenge/smoke/. /home/riemann/tmp/bootstrap-smoke/ && " +
        "chown -R riemann:riemann /home/riemann/tmp/zeta-smoke /home/riemann/tmp/bootstrap-smoke",
      { user: "root", timeoutMs: 60_000 },
    );
    let zetaResult;
    try {
      zetaResult = await sandbox.commands.run(
        "/opt/riemann/tools/bin/lake env lean ZetaRuntimeProbe.lean",
        {
          user: "riemann",
          cwd: "/home/riemann/tmp/zeta-smoke",
          timeoutMs: 4 * 60 * 1_000,
          envs: sandboxEnv,
        },
      );
    } catch (error) {
      const failure = commandFailure(error);
      return {
        sandboxId: sandbox.sandboxId,
        exitCode: failure.exitCode,
        zetaElaborationExitCode: failure.exitCode,
        stdout: failure.stdout,
        stderr: failure.stderr,
        diagnostics: diagnosticsResult.stdout.slice(-4_000),
        failedStage: "zeta-runtime-import" as const,
        networkIsolated: true,
      };
    }
    let result;
    try {
      result = await sandbox.commands.run(
        "bash /opt/riemann/scripts/run-comparator-e2b.sh /opt/riemann/tools/bin/comparator config.json",
        {
          user: "riemann",
          cwd: "/home/riemann/tmp/bootstrap-smoke",
          timeoutMs: 4 * 60 * 1_000,
          envs: sandboxEnv,
        },
      );
    } catch (error) {
      const failure = commandFailure(error);
      return {
        sandboxId: sandbox.sandboxId,
        exitCode: failure.exitCode,
        zetaElaborationExitCode: zetaResult.exitCode,
        stdout: failure.stdout,
        stderr: failure.stderr,
        diagnostics: diagnosticsResult.stdout.slice(-4_000),
        failedStage: "comparator-nanoda" as const,
        networkIsolated: true,
      };
    }
    return {
      sandboxId: sandbox.sandboxId,
      exitCode: result.exitCode,
      zetaElaborationExitCode: zetaResult.exitCode,
      stdout: result.stdout.slice(-4_000),
      stderr: result.stderr.slice(-4_000),
      diagnostics: diagnosticsResult.stdout.slice(-4_000),
      failedStage: null,
      networkIsolated: true,
    };
  } finally {
    await sandbox.kill().catch(() => undefined);
  }
}

function smokeSandboxEnv() {
  return {
    HOME: "/home/riemann",
    PATH: "/opt/riemann/tools/bin:/home/riemann/.elan/bin:/usr/local/bin:/usr/bin:/bin",
    E2B_SANDBOX: "true",
    RIEMANN_E2B_NETWORK_DISABLED: "1",
    COMPARATOR_LANDRUN: "/opt/riemann/tools/bin/landrun",
    COMPARATOR_LEAN4EXPORT: "/opt/riemann/tools/bin/lean4export",
    COMPARATOR_NANODA: "/opt/riemann/tools/bin/nanoda_bin",
  };
}

async function assertSmokeNetworkIsolation(sandbox: E2BSandbox): Promise<void> {
  const info = await sandbox.getInfo();
  if (
    info.allowInternetAccess !== false ||
    !info.network?.denyOut?.includes("0.0.0.0/0")
  ) {
    throw new Error("E2B did not confirm the deny-all outbound rule");
  }
}

async function startExtendedSmokeTemplate(
  templateReference: string,
  key: string,
) {
  const { Sandbox } = await import("e2b");
  const sandbox = await Sandbox.create({
    apiKey: key,
    template: templateReference,
    timeoutMs: 20 * 60 * 1_000,
    secure: true,
    allowInternetAccess: false,
    network: {
      allowPublicTraffic: false,
      denyOut: ["0.0.0.0/0"],
    },
  });

  try {
    await assertSmokeNetworkIsolation(sandbox);
    const diagnostics = await sandbox.commands.run(
      "set -euo pipefail; " +
        "printf 'mathlib_head='; git -C /opt/riemann/zeta23/.lake/packages/mathlib rev-parse HEAD; " +
        "printf 'mathlib_olean='; runuser -u riemann -- test -r /opt/riemann/zeta23/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/CStarAlgebra/Classes.olean && echo readable; " +
        "printf 'tls_egress='; python3 -c 'import socket, ssl; raw = socket.create_connection((\"1.1.1.1\", 443), 3); tls = ssl.create_default_context().wrap_socket(raw, server_hostname=\"one.one.one.one\"); tls.sendall(b\"HEAD / HTTP/1.0\\r\\nHost: one.one.one.one\\r\\n\\r\\n\"); tls.settimeout(3); assert tls.recv(1)' >/dev/null 2>&1 && echo reachable || echo blocked; " +
        "printf 'http_egress='; python3 -c 'import socket; stream = socket.create_connection((\"1.1.1.1\", 80), 3); stream.sendall(b\"HEAD / HTTP/1.0\\r\\nHost: one.one.one.one\\r\\n\\r\\n\"); stream.settimeout(3); assert stream.recv(1)' >/dev/null 2>&1 && echo reachable || echo blocked",
      { user: "root", timeoutMs: 30_000 },
    );
    await sandbox.commands.run(
      "set -euo pipefail; " +
        `rm -rf ${EXTENDED_SMOKE_ROOT} /home/riemann/tmp/zeta-smoke /home/riemann/tmp/bootstrap-smoke && ` +
        `install -d -o riemann -g riemann -m 0700 ${EXTENDED_SMOKE_ROOT} /home/riemann/tmp/zeta-smoke /home/riemann/tmp/bootstrap-smoke && ` +
        "tar --exclude='./.lake' -C /opt/riemann/zeta23 -cf - . | tar -C /home/riemann/tmp/zeta-smoke -xf - && " +
        "install -d -o riemann -g riemann /home/riemann/tmp/zeta-smoke/.lake /home/riemann/tmp/zeta-smoke/.lake/build/lib/lean /home/riemann/tmp/zeta-smoke/.lake/build/ir && " +
        "ln -s /opt/riemann/zeta23/.lake/packages /home/riemann/tmp/zeta-smoke/.lake/packages && " +
        "for artifact_dir in lib/lean ir; do for source in /opt/riemann/zeta23/.lake/build/$artifact_dir/Zeta23 /opt/riemann/zeta23/.lake/build/$artifact_dir/Zeta23.*; do if [ -e \"$source\" ]; then ln -s \"$source\" \"/home/riemann/tmp/zeta-smoke/.lake/build/$artifact_dir/${source##*/}\"; fi; done; done && " +
        "test -s /home/riemann/tmp/zeta-smoke/.lake/build/lib/lean/Zeta23/Unconditional.olean && " +
        "printf '%s\\n' 'import Zeta23.Unconditional' '#check Zeta23.two_thirds_on_critical_line' '#check Zeta23.two_thirds_on_critical_line_cumulative' > /home/riemann/tmp/zeta-smoke/ZetaRuntimeProbe.lean && " +
        "cp -R /opt/riemann/challenge/smoke/. /home/riemann/tmp/bootstrap-smoke/ && " +
        `chown -R riemann:riemann ${EXTENDED_SMOKE_ROOT} /home/riemann/tmp/zeta-smoke /home/riemann/tmp/bootstrap-smoke`,
      { user: "root", timeoutMs: 60_000 },
    );
    await sandbox.files.write(
      `${EXTENDED_SMOKE_ROOT}/run.sh`,
      EXTENDED_SMOKE_SCRIPT,
      { user: "riemann", requestTimeoutMs: 30_000 },
    );
    await sandbox.commands.run(`chmod 0500 ${EXTENDED_SMOKE_ROOT}/run.sh`, {
      user: "riemann",
      timeoutMs: 30_000,
    });
    await sandbox.commands.run(`${EXTENDED_SMOKE_ROOT}/run.sh`, {
      user: "riemann",
      background: true,
      timeoutMs: 30_000,
      envs: smokeSandboxEnv(),
    });
    return {
      sandboxId: sandbox.sandboxId,
      diagnostics: diagnostics.stdout.slice(-4_000),
    };
  } catch (error) {
    await sandbox.kill().catch(() => undefined);
    throw error;
  }
}

async function inspectExtendedSmokeTemplate(sandboxId: string, key: string) {
  const { Sandbox } = await import("e2b");
  const sandbox = await Sandbox.connect(sandboxId, {
    apiKey: key,
    timeoutMs: 20 * 60 * 1_000,
    requestTimeoutMs: 30_000,
  });
  await assertSmokeNetworkIsolation(sandbox);
  const snapshotResult = await sandbox.commands.run(
    `root=${EXTENDED_SMOKE_ROOT}; ` +
      "read_value() { if [[ -f \"$root/$1\" ]]; then tr -d '\\r\\n' < \"$root/$1\"; fi; }; " +
      "read_log() { if [[ -f \"$root/$1\" ]]; then tail -c 4000 \"$root/$1\"; fi; }; " +
      "jq -n " +
      "--arg state \"$(read_value state)\" " +
      "--arg zetaStatus \"$(read_value zeta.status)\" " +
      "--arg zetaSeconds \"$(read_value zeta.seconds)\" " +
      "--arg comparatorStatus \"$(read_value comparator.status)\" " +
      "--arg comparatorSeconds \"$(read_value comparator.seconds)\" " +
      "--arg zetaLog \"$(read_log zeta.log)\" " +
      "--arg comparatorLog \"$(read_log comparator.log)\" " +
      "'{state: (if $state == \"\" then \"starting\" else $state end), zetaStatus: $zetaStatus, zetaSeconds: $zetaSeconds, comparatorStatus: $comparatorStatus, comparatorSeconds: $comparatorSeconds, zetaLog: $zetaLog, comparatorLog: $comparatorLog}'",
    { user: "riemann", timeoutMs: 30_000 },
  );
  const snapshot = JSON.parse(snapshotResult.stdout) as {
    state: string;
    zetaStatus: string;
    zetaSeconds: string;
    comparatorStatus: string;
    comparatorSeconds: string;
    zetaLog: string;
    comparatorLog: string;
  };
  const completed = snapshot.state === "done";
  const passed =
    completed &&
    snapshot.zetaStatus === "0" &&
    snapshot.comparatorStatus === "0";
  if (completed) await sandbox.kill().catch(() => undefined);
  return {
    status: completed ? (passed ? "passed" : "failed") : "running",
    stage: snapshot.state || "starting",
    sandboxId,
    networkIsolated: true,
    zetaElaborationExitCode: snapshot.zetaStatus
      ? Number(snapshot.zetaStatus)
      : null,
    zetaSeconds: snapshot.zetaSeconds ? Number(snapshot.zetaSeconds) : null,
    comparatorExitCode: snapshot.comparatorStatus
      ? Number(snapshot.comparatorStatus)
      : null,
    comparatorSeconds: snapshot.comparatorSeconds
      ? Number(snapshot.comparatorSeconds)
      : null,
    zetaLog: snapshot.zetaLog,
    comparatorLog: snapshot.comparatorLog,
  };
}

export async function POST(request: Request): Promise<Response> {
  if (!authorized(request)) return noStore(401, { error: "unauthorized" });
  const url = new URL(request.url);
  const action = url.searchParams.get("action");

  try {
    const key = apiKey();
    if (action === "smoke-status") {
      const sandboxId = url.searchParams.get("sandboxId");
      if (!sandboxId || !identifierPattern.test(sandboxId)) {
        return noStore(400, { error: "invalid_smoke_sandbox_id" });
      }
      const smoke = await inspectExtendedSmokeTemplate(sandboxId, key);
      return noStore(smoke.status === "failed" ? 422 : 200, smoke);
    }
    if (action === "smoke-start") {
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
      const smoke = await startExtendedSmokeTemplate(templateReference, key);
      return noStore(202, {
        status: "running",
        stage: "zeta-runtime-import",
        templateId,
        buildId,
        templateReference,
        ...smoke,
      });
    }
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
      const smoke = await smokeTemplate(templateReference, key);
      const passed =
        smoke.exitCode === 0 && smoke.zetaElaborationExitCode === 0;
      return noStore(passed ? 200 : 422, {
        status: passed ? "passed" : "failed",
        templateId,
        buildId,
        templateReference,
        smoke,
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
