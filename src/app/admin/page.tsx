import { competitions } from "@/lib/competitions";
import Link from "next/link";
import { notFound, redirect } from "next/navigation";
import { getSession } from "@/auth";
import { WorkspaceHeader, Metrics, resultLabel } from "@/components/account-workspace";
import styles from "@/components/account-workspace.module.css";
import { isSubmissionArchiveMaintainer, readSubmissionArchive, readVerificationDesk } from "@/lib/submission-archive-store";

export const dynamic = "force-dynamic";
export const metadata = { title: "Verification desk", robots: { index: false, follow: false, noarchive: true } };
const date = new Intl.DateTimeFormat("en-GB", { timeZone: "UTC", dateStyle: "medium", timeStyle: "short" });
const outcomes = ["promoted", "rejected", "superseded", "publication-blocked", "archived"];
const perPage = 25;

export default async function Admin({ searchParams }: { searchParams: Promise<{ q?: string; result?: string; page?: string; attempt?: string }> }) {
  const user = (await getSession())?.user;
  if (!user?.githubLogin) redirect("/signin?view=admin");
  if (!isSubmissionArchiveMaintainer(user.githubLogin, user.githubId)) notFound();
  const desk = await readVerificationDesk(user.githubLogin, user.githubId).catch(error => {
    console.error("Unable to load verification desk", error); return null;
  });
  const params = await searchParams;
  const q = typeof params.q === "string" ? params.q.trim().toLowerCase().slice(0, 100) : "";
  const result = outcomes.includes(params.result ?? "") ? params.result! : "";
  const matches = desk?.attempts.filter(row => (!result || row.status === result) && (row.jobId.includes(q) || row.digest.includes(q))) ?? [];
  const totalPages = Math.max(1, Math.ceil(matches.length / perPage));
  const page = Math.min(totalPages, Math.max(1, Number.parseInt(params.page ?? "1", 10) || 1));
  const pageLink = (n: number) => `/admin?${new URLSearchParams({ q, result, page: String(n) })}#attempts`;
  const selected = params.attempt && desk ? [...desk.live, ...desk.attempts].find(row => row.jobId === params.attempt) : undefined;
  const submission = selected?.sourceId
    ? await readSubmissionArchive(selected.sourceId).then(entry => entry?.summary).catch(() => undefined)
    : undefined;
  function detailLink(id: string) {
    return `/admin?${new URLSearchParams({ q, result, page: String(page), attempt: id })}#attempt`;
  }
  function rowView(row: NonNullable<typeof desk>["attempts"][number]) {
    const source = row.sourceId && `/api/admin/submission-archive/${row.sourceId}`;
    return <li className={styles.row} key={row.jobId}>
      <div><time dateTime={row.date}>{date.format(new Date(row.date))} UTC</time><small>{resultLabel(row.status)}</small></div>
      <div><small>Job</small><code title={row.jobId}>{row.jobId}</code></div>
      <div><small>SHA-256</small><code title={row.digest}>{row.digest.slice(0, 12)}…</code></div>
      <div>{row.message && <small>{row.message}</small>}<div className={styles.actions}>
        {source && <Link prefetch={false} href={detailLink(row.jobId)}>Details</Link>}
        {source && <a href={source} target="_blank" rel="noreferrer">Source</a>}
        {row.hasLog && <a href={`/api/admin/submission-archive/${row.jobId}?log=1`} target="_blank" rel="noreferrer">Log</a>}
        {row.evidenceUrl && <a href={row.evidenceUrl}>Evidence</a>}
      </div></div>
    </li>;
  }
  return <main id="main-content" className={styles.workspace}>
    <WorkspaceHeader admin maintainer github={user.githubLogin}><a className="button button-dark" href={pageLink(page).split("#")[0]}>Refresh queue</a></WorkspaceHeader>
    {desk ? <>
      <Metrics items={[{label:"Active worker jobs",value:desk.active},{label:"Waiting in queue",value:desk.waiting},{label:"Archived sources",value:desk.sources}]} />
      {params.attempt && <section id="attempt" className="history-detail" aria-label="Selected attempt">
        {selected && submission ? <>
          <h2>{submission.submission.id}</h2>
          <p>{submission.submission.author.displayName} · @{submission.submission.author.github} · {resultLabel(selected.status)}</p>
          <dl className={styles.facts}>
            <dt>Challenge</dt><dd>{competitions[submission.submission.track].title}</dd>
            <dt>Claimed bound</dt><dd>{submission.submission.score.numerator} / {submission.submission.score.denominator}</dd>
            <dt>Method</dt><dd>{submission.submission.method}</dd>
            <dt>Job</dt><dd><code>{selected.jobId}</code></dd>
            <dt>Proof SHA-256</dt><dd><code>{selected.digest}</code></dd>
            <dt>Source size</dt><dd>{submission.sourceBytes.toLocaleString("en-US")} bytes</dd>
          </dl>
          <div className={styles.actions}><a href={`/api/admin/submission-archive/${selected.sourceId}?download=1`}>Download Lean source</a>
            {"hasLog" in selected && selected.hasLog && <a href={`/api/admin/submission-archive/${selected.jobId}?log=1`}>Recorded verifier log</a>}
            <Link href={pageLink(page)}>Close details</Link>
          </div>
        </> : <p>Details for this attempt are unavailable.</p>}
      </section>}
      <section className={styles.section}><h2>Current queue</h2>
        {desk.live.length ? <ol className={styles.list}>{desk.live.map(rowView)}</ol> : <p className={styles.empty}>Queue empty. No proofs are waiting for verification.</p>}
      </section>
      <section id="attempts" className={styles.section}><h2>Submission archive</h2>
        <form className={styles.filters} action="/admin#attempts">
          <label>Job ID or proof digest<input type="search" name="q" defaultValue={q} maxLength={100} /></label>
          <label>Outcome<select name="result" defaultValue={result}><option value="">All outcomes</option>{outcomes.map(s=><option key={s} value={s}>{resultLabel(s)}</option>)}</select></label>
          <button className="button button-dark" type="submit">Filter</button>
          {(q || result) && <Link className={styles.textlink} href="/admin#attempts">Clear filters</Link>}
        </form>
        {matches.length ? <>
          <p>{matches.length} matching {matches.length === 1 ? "attempt" : "attempts"}</p>
          <ul className={styles.list}>{matches.slice((page-1)*perPage,page*perPage).map(rowView)}</ul>
          {totalPages > 1 && <nav className={styles.pages} aria-label="Archive pages">{page>1 && <Link className={styles.textlink} href={pageLink(page-1)}>Previous</Link>}<span>Page {page} of {totalPages}</span>{page<totalPages && <Link className={styles.textlink} href={pageLink(page+1)}>Next</Link>}</nav>}
        </> : <p className={styles.empty}>{q || result ? "No attempts match these filters." : "No archived attempts yet."}</p>}
      </section>
    </> : <p className={styles.empty} role="alert">The verification desk could not load the queue. Refresh to retry.</p>}
  </main>;
}
