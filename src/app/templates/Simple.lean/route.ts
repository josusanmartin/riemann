import { readFileSync } from "node:fs";

export const dynamic = "force-static";

export function GET(): Response {
  return new Response(readFileSync("challenge/templates/Simple.Candidate.lean", "utf8"), {
    headers: {
      "Content-Type": "text/plain; charset=utf-8",
      "Content-Disposition": 'attachment; filename="Solution.lean"',
    },
  });
}
