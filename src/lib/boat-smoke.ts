import "server-only";

const sandboxIdPattern = /^bx_[23456789abcdefghjkmnpqrstuvwxyz]{8}$/;

export function isBoatSmokeConfigured(): boolean {
  return Boolean(process.env.BOAT_API_KEY && sandboxIdPattern.test(process.env.RIEMANN_BOAT_SANDBOX_ID ?? ""));
}

export async function runBoatSmoke(): Promise<"passed" | "failed" | "busy"> {
  if (!isBoatSmokeConfigured()) throw new Error("Boat configuration missing");
  const id = process.env.RIEMANN_BOAT_SANDBOX_ID;
  const response = await fetch(`https://boat.dev/api/v1/sandboxes/${id}/commands`, {
    method: "POST",
    headers: { Authorization: `Bearer ${process.env.BOAT_API_KEY}`, "Content-Type": "application/json" },
    body: JSON.stringify({
      command: 'bash "$HOME/.local/share/riemann-boat/site/scripts/boat-smoke.sh"',
      timeoutSeconds: 120,
    }),
    cache: "no-store",
    redirect: "error",
    signal: AbortSignal.timeout(150_000),
  });
  if (!response.ok) throw new Error(`Boat HTTP ${response.status}`);
  const result = await response.json();
  if (result.ok !== true || result.type !== "command.finished") throw new Error("Incomplete command");
  if (result.timedOut || result.launcherFailed || result.oomKilled || result.signal) return "failed";
  if (result.exitCode === 75) return "busy";
  return result.success === true && result.exitCode === 0 && result.stdout?.trim() === "BOAT_SMOKE_OK"
    ? "passed" : "failed";
}
