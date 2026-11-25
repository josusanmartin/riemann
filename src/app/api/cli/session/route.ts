import { guardUserApi } from "@/lib/api-guard";
import { cliBearerPrefix } from "@/lib/cli-login";
import { getSubmissionSession } from "@/lib/submission-session";

export async function GET(request: Request) {
  const denied = guardUserApi(request, "poll");
  if (denied) return denied;
  const auth = request.headers.get("authorization");
  const session = auth ? await getSubmissionSession(request) : null;
  const headers = { "Cache-Control": "private, no-store" };
  if (!session?.user.githubId) {
    const website = auth?.startsWith(cliBearerPrefix);
    const error = !auth ? "authentication_required" : website ? "invalid_cli_session" : "github_identity_unavailable";
    const message = !auth ? "Run riemann login to authenticate." : website
      ? "The website could not verify this CLI credential. Use the approval from the same login request, or start a fresh login."
      : "GitHub identity could not be verified. Check the token supplied in RIEMANN_GITHUB_TOKEN or unset it and use riemann login.";
    return Response.json({ error, message }, { status: 401, headers });
  }
  return Response.json({ githubLogin: session.user.githubLogin,
    ...(auth?.startsWith(cliBearerPrefix) ? { expires: session.expires, source: "website-login" } : { source: "github-token" }),
  }, { headers });
}
