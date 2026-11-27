import { isPublicationMismatch, publicationMismatchMessage } from "@/lib/publication-feedback";
import Link from "next/link";
import { ArrowLeft } from "lucide-react";
import { redirect } from "next/navigation";
import { getSession } from "@/auth";
import { readOwnerHistory } from "@/lib/submission-archive-store";
import { privateDiagnostic } from "@/lib/private-diagnostic";
import { describeVerifierRejection } from "@/lib/verifier-feedback";

export const dynamic = "force-dynamic";
export const metadata = { title: "My submission history", robots: { index: false, follow: false } };

function time(iso: string) {
  return new Date(iso).toLocaleString("en-GB", { timeZone: "UTC", dateStyle: "medium", timeStyle: "short" });
}

export default async function History({ searchParams }: { searchParams: Promise<{ attempt?: string }> }) {
  const user = (await getSession())?.user;
  const github = user?.githubLogin;
  if (!github) redirect("/signin");
  const { attempt } = await searchParams;
  const history = await readOwnerHistory(github, attempt, { githubId: user?.githubId }).catch(error => {
    console.error("Unable to load submission history", error);
    return null;
  });
  const detail = history?.detail;
  const receipt = detail?.receipt;
  const blocked = receipt?.outcome === "publication-blocked" || isPublicationMismatch(receipt?.message);
  const finalLog = detail?.logs.find(log => log.jobId === receipt?.jobId)?.log;
  const excerpt = receipt?.outcome === "rejected" ? privateDiagnostic(finalLog) : undefined;
  const diagnostic = receipt?.outcome === "rejected"
    ? receipt.feedback ?? describeVerifierRejection(finalLog ?? "", receipt.message ?? "")
    : null;
  return (
    <main id="main-content" className="submission-history">
      <header className="history-heading">
        <Link className="history-back" href="/submit"><ArrowLeft size={15} aria-hidden="true" /> Submit a proof</Link>
        <h1>My submission history</h1>
        <p>@{github}</p>
      </header>
      {history ? <>
        {detail && receipt ? (
          <section className="history-detail" aria-label="Attempt details">
            <h2>{diagnostic?.title ?? (blocked ? "Verified · publication blocked" : receipt.outcome === "promoted" ? "Published" : "Superseded")}</h2>
            <p><time dateTime={receipt.completedAt}>{time(receipt.completedAt)} UTC</time></p>
            <p>{blocked ? publicationMismatchMessage : diagnostic?.detail ?? receipt.message}</p>
            {diagnostic && receipt.message && receipt.message !== diagnostic.detail && (
              <p>Recorded message: <code>{receipt.message}</code></p>
            )}
            {diagnostic && <p>{diagnostic.stage} · <code>{diagnostic.code}</code></p>}
            {diagnostic?.location && <p>Source location <code>{diagnostic.location.file}:{diagnostic.location.line}:{diagnostic.location.column}</code></p>}
            {excerpt && <><h3>First diagnostic in the retained output</h3><pre>{excerpt}</pre></>}
            {diagnostic && <p>{diagnostic.action}</p>}
            <p>Proof SHA-256 <code>{receipt.proofDigest}</code></p>
            <p>Job <code>{receipt.jobId}</code></p>
            {detail.logs.length ? detail.logs.map(log => <details key={log.jobId} open={!excerpt}>
              <summary>{log.jobId === receipt.jobId ? "Recorded verifier output" : "First worker output"}</summary>
              {log.omittedBytes > 0 && <p>{log.omittedBytes} earlier bytes were omitted.</p>}
              <pre>{log.log}</pre>
            </details>) : !detail.unavailable && <p>No worker output was retained for this attempt.</p>}
            {detail.unavailable && <p>Some archived output could not be retrieved. Refresh to retry, or share the job ID with the maintainers.</p>}
          </section>
        ) : attempt && <p>Attempt details are unavailable for this account.</p>}
        {history.active.length + history.completed.length ? <div className="archive-table-wrap">
          <table className="archive-table">
            <thead><tr><th scope="col">Attempt (UTC)</th><th scope="col">Result</th><th scope="col"><span className="sr-only">Details</span></th></tr></thead>
            <tbody>
              {history.active.map(row => <tr key={row.jobId}><td><time dateTime={row.date}>{time(row.date)}</time><code title={row.digest} aria-label={`Proof SHA-256 prefix ${row.digest.slice(0, 12)}`}>{row.digest.slice(0, 12)}</code></td><td>{row.status}</td>
                <td></td></tr>)}
              {history.completed.map(row => <tr key={row.jobId}><td><time dateTime={row.date}>{time(row.date)}</time><code title={row.digest} aria-label={`Proof SHA-256 prefix ${row.digest.slice(0, 12)}`}>{row.digest.slice(0, 12)}</code></td>
                <td>{row.status === "promoted" ? "Published" : row.status === "rejected" ? "Unsuccessful" : row.status === "publication-blocked" ? "Publication blocked" : "Superseded"}</td>
                <td><Link className="text-link" prefetch={false} href={`/submit/history?attempt=${row.jobId}`}>Details</Link></td>
              </tr>)}
            </tbody>
          </table>
        </div> : <p>No admitted submissions yet.</p>}
      </> : <p role="alert">Your history is temporarily unavailable. Refresh to retry.</p>}
    </main>
  );
}
