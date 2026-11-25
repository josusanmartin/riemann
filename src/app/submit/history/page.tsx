import Link from "next/link";
import { redirect } from "next/navigation";
import { getSession } from "@/auth";
import { readOwnerHistory } from "@/lib/submission-archive-store";
import { describeVerifierRejection } from "@/lib/verifier-feedback";

export const dynamic = "force-dynamic";
export const metadata = { title: "My submission history", robots: { index: false, follow: false } };

function time(iso: string) {
  return new Date(iso).toLocaleString("en-GB", { timeZone: "UTC", dateStyle: "medium", timeStyle: "short" });
}

export default async function History({ searchParams }: { searchParams: Promise<{ attempt?: string }> }) {
  const github = (await getSession())?.user.githubLogin;
  if (!github) redirect("/signin");
  const { attempt } = await searchParams;
  const history = await readOwnerHistory(github, attempt).catch(error => {
    console.error("Unable to load submission history", error);
    return null;
  });
  const detail = history?.detail;
  const receipt = detail?.receipt;
  const diagnostic = receipt?.outcome === "rejected"
    ? receipt.feedback ?? describeVerifierRejection("", receipt.message ?? "")
    : null;
  return (
    <main id="main-content" className="shell section-space archive-section">
      <Link className="text-link" href="/submit">← Submit a proof</Link>
      <h1>My submission history</h1>
      <p>Attempts for @{github}. All times are UTC.</p>
      {history ? <>
        {detail && receipt ? (
          <section className="history-detail" aria-label="Attempt details">
            <h2>{diagnostic?.title ?? (receipt.outcome === "promoted" ? "Published" : "Superseded")}</h2>
            <p><time dateTime={receipt.completedAt}>{time(receipt.completedAt)} UTC</time></p>
            <p>{diagnostic?.detail ?? receipt.message}</p>
            {diagnostic && receipt.message && receipt.message !== diagnostic.detail && (
              <p>Recorded message: <code>{receipt.message}</code></p>
            )}
            {diagnostic && <p>{diagnostic.action}</p>}
            <p>Proof SHA-256 <code>{receipt.proofDigest}</code></p>
            <p>Job <code>{receipt.jobId}</code></p>
            {detail.logs.length ? detail.logs.map(log => <details key={log.jobId} open>
              <summary>{log.jobId === receipt.jobId ? "Recorded output (last 100,000 characters)" : "First worker output"}</summary>
              {log.omittedBytes > 0 && <p>{log.omittedBytes} earlier bytes were omitted.</p>}
              <pre>{log.log}</pre>
            </details>) : <p>No worker output was retained for this attempt.</p>}
          </section>
        ) : attempt && <p>Attempt details are unavailable for this account.</p>}
        {history.active.length + history.completed.length ? <div className="archive-table-wrap">
          <table className="archive-table">
            <thead><tr><th>Time (UTC)</th><th>Result</th><th>SHA-256</th><th>Attempt</th></tr></thead>
            <tbody>
              {history.active.map(row => <tr key={row.jobId}><td>{time(row.date)}</td><td>{row.status}</td>
                <td><code>{row.digest.slice(0, 12)}</code></td><td>In queue</td></tr>)}
              {history.completed.map(row => <tr key={row.jobId}><td>{time(row.date)}</td>
                <td>{row.status === "promoted" ? "Published" : row.status === "rejected" ? "Unsuccessful" : "Superseded"}</td>
                <td><code>{row.digest.slice(0, 12)}</code></td>
                <td><Link className="text-link" prefetch={false} href={`/submit/history?attempt=${row.jobId}`}>View details</Link></td>
              </tr>)}
            </tbody>
          </table>
        </div> : <p>No admitted submissions yet.</p>}
      </> : <p role="alert">Your history is temporarily unavailable. Refresh to retry.</p>}
    </main>
  );
}
