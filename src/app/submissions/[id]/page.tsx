import type { Metadata } from "next";
import Link from "next/link";
import { notFound } from "next/navigation";
import { ArrowLeft, ArrowUpRight, BadgeCheck, BookOpen, CalendarDays, CircleDot, UserCheck, UserRound } from "lucide-react";
import { getRecord, getRecords } from "@/lib/records";
import { truncateDecimalString } from "@/components/format";

type PageProps = { params: Promise<{ id: string }> };

export function generateStaticParams() {
  return getRecords().map((record) => ({ id: record.id }));
}

export async function generateMetadata({ params }: PageProps): Promise<Metadata> {
  const record = getRecord((await params).id);
  return record ? { title: `${record.author} · ${record.scorePercent.slice(0, 12)}%`, description: record.summary } : { title: "Record not found" };
}

export default async function SubmissionPage({ params }: PageProps) {
  const record = getRecord((await params).id);
  if (!record) notFound();

  return (
    <main id="main-content">
      <section className="record-hero shell-wrap">
        <div className="shell">
          <Link className="back-link back-link-light" href="/#leaderboard"><ArrowLeft size={15} /> Back to record ledger</Link>
          <div className="record-hero-grid">
            <div>
              <div className="verification-badges">
                <span className={`verification-badge ${record.formalVerification ? "verified" : "paper"}`}>
                  {record.formalVerification ? <BadgeCheck size={16} /> : <BookOpen size={16} />}
                  {record.formalVerification ? "Kernel verified" : "Published result"}
                </span>
                {record.independentReview && (
                  <a className="verification-badge expert" href={record.independentReview.url} target="_blank" rel="noreferrer">
                    <UserCheck size={16} /> Expert reviewed
                  </a>
                )}
              </div>
              <h1>{record.title}</h1>
              <p>{record.summary}</p>
            </div>
            <div className="record-big-score"><span>Certified lower bound</span><strong>{truncateDecimalString(record.scorePercent, record.formalVerification ? 10 : 4)}<sup>%</sup></strong><code>κ = {record.exactExpression}</code></div>
          </div>
        </div>
      </section>

      <section className="shell record-details">
        <article>
          <span className="eyebrow">Record evidence</span>
          <h2>{record.author}</h2>
          <dl className="record-metadata">
            <div><dt><CalendarDays size={16} /> Date</dt><dd>{new Date(`${record.date}T00:00:00Z`).toLocaleDateString("en-US", { year: "numeric", month: "long", day: "numeric", timeZone: "UTC" })}</dd></div>
            <div><dt><UserRound size={16} /> Author</dt><dd>{record.github ? `@${record.github}` : record.author}</dd></div>
            <div><dt><CircleDot size={16} /> Method</dt><dd>{record.method}</dd></div>
          </dl>
        </article>
        <aside className="evidence-card">
          <span className="eyebrow">Primary source</span>
          <h3>{record.formalVerification ? "Machine-checkable proof" : "Peer-reviewed paper"}</h3>
          <p>{record.formalVerification ? "Replay the public Lean source against the pinned formal definitions." : "This historical point is sourced to the published mathematical literature and is not yet formalized here."}</p>
          <a className="button button-dark" href={record.proofUrl ?? record.sourceUrl} target="_blank" rel="noreferrer">Open evidence <ArrowUpRight size={16} /></a>
          {record.proofUrl && record.proofUrl !== record.sourceUrl && <a className="text-link" href={record.sourceUrl} target="_blank" rel="noreferrer">Read the research paper <ArrowUpRight size={14} /></a>}
          <div className={`independent-review ${record.independentReview ? "reviewed" : "unreviewed"}`}>
            <UserCheck size={18} />
            <div>
              <strong>Independent expert review</strong>
              {record.independentReview ? (
                <>
                  <span>{record.independentReview.reviewer} · {record.independentReview.date}</span>
                  <p>{record.independentReview.summary}</p>
                  <a href={record.independentReview.url} target="_blank" rel="noreferrer">Read review <ArrowUpRight size={13} /></a>
                </>
              ) : (
                <span>Optional and not recorded. This does not affect formal acceptance.</span>
              )}
            </div>
          </div>
        </aside>
      </section>
    </main>
  );
}
