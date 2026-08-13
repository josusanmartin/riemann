import { getSession } from "@/auth";
import {
  isSubmissionArchiveMaintainer,
  readSubmissionArchive,
} from "@/lib/submission-archive-store";

export const runtime = "nodejs";
export const maxDuration = 60;
export const dynamic = "force-dynamic";

type RouteContext = { params: Promise<{ jobId: string }> };

function json(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "private, no-store, max-age=0" },
  });
}

export async function GET(
  request: Request,
  { params }: RouteContext,
): Promise<Response> {
  const session = await getSession();
  if (!isSubmissionArchiveMaintainer(session?.user.githubLogin)) {
    return json(404, { error: "not_found" });
  }

  try {
    const archived = await readSubmissionArchive((await params).jobId);
    if (!archived) return json(404, { error: "archive_not_found" });
    const download = new URL(request.url).searchParams.get("download") === "1";
    const filename = `${archived.summary.submission.id}-Solution.lean`;
    return new Response(archived.payload.solution, {
      status: 200,
      headers: {
        "Cache-Control": "private, no-store, max-age=0",
        "Content-Disposition": `${download ? "attachment" : "inline"}; filename="${filename}"`,
        "Content-Security-Policy": "default-src 'none'; sandbox",
        "Content-Type": "text/plain; charset=utf-8",
        "X-Content-Type-Options": "nosniff",
        "X-Riemann-Proof-Digest": archived.payload.proofDigest,
        "X-Robots-Tag": "noindex, nofollow, noarchive",
      },
    });
  } catch (error) {
    console.error("Unable to decrypt the requested submission archive", error);
    return json(502, {
      error: "archive_unavailable",
      message: "The encrypted source archive could not be read.",
    });
  }
}
