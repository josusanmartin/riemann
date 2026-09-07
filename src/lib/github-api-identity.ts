import { z } from "zod";
import { githubLoginSchema } from "./challenge";

const identitySchema = z.object({
  id: z.number().int().positive(),
  login: githubLoginSchema,
  name: z.string().nullable(),
  type: z.literal("User"),
});

/** Authenticate CLI requests with GitHub itself. Never persist or log tokens. */
export async function githubApiIdentity(request: Request, fetcher = fetch) {
  const authorization = request.headers.get("authorization");
  if (!authorization || !/^Bearer [A-Za-z0-9_]{20,255}$/.test(authorization)) return null;
  try {
    const response = await fetcher("https://api.github.com/user", {
      headers: {
        Authorization: authorization,
        Accept: "application/vnd.github+json",
        "X-GitHub-Api-Version": "2026-03-10",
      },
      cache: "no-store",
      redirect: "error",
      signal: AbortSignal.timeout(10_000),
    });
    if (!response.ok) return null;
    const parsed = identitySchema.safeParse(await response.json());
    return parsed.success ? parsed.data : null;
  } catch {
    return null;
  }
}
