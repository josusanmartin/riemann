import { guardUserApi } from "@/lib/api-guard";
import { cliBearerPrefix } from "@/lib/cli-login";
import { getSubmissionSession } from "@/lib/submission-session";

export async function GET(request: Request) {
  const denied = guardUserApi(request, "poll");
  if (denied) return denied;
  const auth = request.headers.get("authorization");
  const session = auth ? await getSubmissionSession(request) : null;
  const headers = { "Cache-Control": "private, no-store" };
  if (!session?.user.githubId) return Response.json({ message: "Sign in with riemann login." }, { status: 401, headers });
  return Response.json({ githubLogin: session.user.githubLogin,
    ...(auth?.startsWith(cliBearerPrefix) ? { expires: session.expires, source: "website-login" } : { source: "github-token" }),
  }, { headers });
}
