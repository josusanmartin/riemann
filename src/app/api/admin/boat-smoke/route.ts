import { getSession } from "@/auth";
import { isFlowTestOperator } from "@/lib/flow-test";
import { isBoatSmokeConfigured, runBoatSmoke } from "@/lib/boat-smoke";

export const runtime = "nodejs";
export const maxDuration = 180;

function reply(status: number, message: string) {
  return Response.json({ message }, { status, headers: { "Cache-Control": "no-store" } });
}

export async function POST(request: Request) {
  const origin = request.headers.get("origin");
  if (origin && origin !== new URL(request.url).origin) return reply(403, "Invalid origin.");
  if (request.headers.get("content-type")?.split(";")[0] !== "application/json") {
    return reply(415, "Send a JSON request.");
  }
  const login = (await getSession(request))?.user.githubLogin;
  if (!login) return reply(401, "Sign in to run this test.");
  if (!isFlowTestOperator(login)) return reply(403, "Site operator access is required.");
  if (!isBoatSmokeConfigured()) return reply(503, "Boat smoke testing is not configured.");
  try {
    const result = await runBoatSmoke();
    if (result === "busy") return reply(409, "A Boat smoke test is already running.");
    if (result === "failed") return reply(422, "The Boat verification checks failed.");
    return reply(200, "Lean and nanoda accepted the fixture. Comparator rejected the changed theorem statement.");
  } catch {
    return reply(502, "Boat could not complete the test. Check the sandbox state and command history.");
  }
}
