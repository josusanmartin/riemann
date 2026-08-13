import type { Metadata } from "next";
import Link from "next/link";
import { notFound, redirect } from "next/navigation";
import { Download, ExternalLink, FileCode2, LockKeyhole } from "lucide-react";
import { getSession, isGitHubAuthConfigured } from "@/auth";
import {
  isSubmissionArchiveMaintainer,
  listSubmissionArchive,
  type SubmissionArchiveEntry,
} from "@/lib/submission-archive-store";

export const metadata: Metadata = {
  title: "Private proof archive",
  robots: { index: false, follow: false, noarchive: true },
};

export const dynamic = "force-dynamic";

function formatBytes(bytes: number): string {
  if (bytes < 1024) return `${bytes} B`;
  return `${(bytes / 1024).toFixed(1)} KB`;
}

export default async function SubmissionArchivePage() {
  const session = await getSession();
  const github = session?.user.githubLogin;
  if (!github) {
    if (isGitHubAuthConfigured) redirect("/signin");
    notFound();
  }
  if (!isSubmissionArchiveMaintainer(github)) notFound();

  let entries: SubmissionArchiveEntry[];
  let error: string | null = null;
  try {
    entries = await listSubmissionArchive();
  } catch (caught) {
    console.error("Unable to list the encrypted submission archive", caught);
    entries = [];
    error = "The encrypted archive could not be listed right now.";
  }

  return (
    <main id="main-content">
      <section className="inner-hero shell-wrap archive-hero">
        <div className="shell inner-hero-grid">
          <div>
            <span className="eyebrow">Maintainer only</span>
            <h1>Private Lean submission archive</h1>
            <p>
              Every admitted upload is encrypted before it is committed with its
              queue entry. Open or download a source here without exposing it on
              the public submission ledger.
            </p>
          </div>
          <aside className="submit-status-card">
            <LockKeyhole size={25} />
            <strong>AES-256-GCM encrypted at rest</strong>
            <p>
              Access requires the archive key in Vercel and an authenticated
              maintainer GitHub account. Responses are private and never cached.
            </p>
          </aside>
        </div>
      </section>

      <section className="shell section-space archive-section">
        <div className="section-heading split-heading">
          <div>
            <span className="eyebrow">Retained attempts</span>
            <h2>{entries.length} encrypted source{entries.length === 1 ? "" : "s"}</h2>
          </div>
          <p>
            Retention starts with the archive deployment. The earlier lost
            <code> 3d0b… </code> sandbox cannot be reconstructed retroactively.
          </p>
        </div>

        {error ? (
          <div className="archive-empty"><strong>Archive unavailable</strong><p>{error}</p></div>
        ) : entries.length === 0 ? (
          <div className="archive-empty">
            <FileCode2 size={26} />
            <strong>No retained submissions yet</strong>
            <p>The next admitted Lean upload will appear here atomically with queue admission.</p>
          </div>
        ) : (
          <div className="archive-table-wrap">
            <table className="archive-table">
              <thead>
                <tr><th>Submitted</th><th>Proof digest</th><th>Job</th><th>Encrypted</th><th>Source</th></tr>
              </thead>
              <tbody>
                {entries.map((entry) => {
                  const sourceUrl = `/api/admin/submission-archive/${entry.jobId}`;
                  return (
                    <tr key={entry.jobId}>
                      <td>{new Date(entry.submittedAt).toLocaleString("en-US", { timeZone: "UTC", dateStyle: "medium", timeStyle: "medium" })} UTC</td>
                      <td><code>sha256:{entry.proofDigest.slice(0, 12)}…</code></td>
                      <td><code>{entry.jobId.slice(0, 8)}…</code></td>
                      <td>{formatBytes(entry.encryptedBytes)}</td>
                      <td className="archive-actions">
                        <a href={sourceUrl} target="_blank" rel="noreferrer">Review <ExternalLink size={13} /></a>
                        <a href={`${sourceUrl}?download=1`}><Download size={13} /> Download</a>
                      </td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
        )}

        <Link className="text-link archive-back" href="/submit">Back to proof submission</Link>
      </section>
    </main>
  );
}
