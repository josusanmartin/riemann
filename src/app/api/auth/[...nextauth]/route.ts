import { handlers, isGitHubAuthConfigured } from "@/auth";

function unavailable(): Response {
  return Response.json(
    {
      error: "github_auth_not_configured",
      message: "GitHub sign-in will be enabled after production OAuth is configured.",
    },
    {
      status: 503,
      headers: { "Cache-Control": "no-store" },
    },
  );
}

export const GET = isGitHubAuthConfigured ? handlers.GET : unavailable;
export const POST = isGitHubAuthConfigured ? handlers.POST : unavailable;
