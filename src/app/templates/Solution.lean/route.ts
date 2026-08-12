import { submissionStarterSource } from "@/lib/submission-starter";

export const dynamic = "force-static";

export function GET(): Response {
  return new Response(submissionStarterSource, {
    status: 200,
    headers: {
      "Cache-Control": "public, max-age=0, must-revalidate",
      "Content-Disposition": 'attachment; filename="Solution.lean"',
      "Content-Type": "text/plain; charset=utf-8",
      "X-Content-Type-Options": "nosniff",
    },
  });
}
