import type { Metadata } from "next";
import Link from "next/link";
import { ArrowUpRight, BadgeCheck, BookOpen, GitPullRequestArrow } from "lucide-react";
import { getRecords } from "@/lib/records";
import { repositoryUrl } from "@/lib/site";
import { truncateDecimalString } from "@/components/format";

export const metadata: Metadata = {
  title: "Submissions",
  description:
    "Every accepted critical-line record, newest first, plus the open candidate pull requests awaiting verification.",
};

export default function SubmissionsIndexPage() {
  const records = [...getRecords()].reverse();

  return (
    <main id="main-content">
      <section className="shell section-space submissions-index">
        <span className="eyebrow">Record ledger</span>
        <h1>Every accepted record</h1>
        <p className="submissions-lede">
          Newest first. Each entry links to its evidence; values are truncated, never rounded up. Open candidates
          live as public pull requests until the verifier promotes a strict improvement.
        </p>
        <ol className="submissions-list">
          {records.map((record) => (
            <li key={record.id}>
              <Link href={`/submissions/${record.id}`} className="submissions-item">
                <span className="submissions-year">{record.date.slice(0, 4)}</span>
                <span className="submissions-main">
                  <strong>{record.title}</strong>
                  <small>{record.author} · {record.method}</small>
                </span>
                <span className="submissions-score">
                  {truncateDecimalString(record.scorePercent, record.formalVerification ? 10 : 4)}%
                </span>
                <span className={record.formalVerification ? "submissions-badge verified" : "submissions-badge"}>
                  {record.formalVerification ? <BadgeCheck size={15} /> : <BookOpen size={15} />}
                  {record.formalVerification ? "Kernel" : "Paper"}
                </span>
              </Link>
            </li>
          ))}
        </ol>
        <div className="submissions-open">
          <GitPullRequestArrow size={20} />
          <p>
            <strong>Working on a candidate?</strong> Open pull requests stay public on GitHub while the verifier
            replays them against the pinned contract.
          </p>
          <a className="button button-dark" href={`${repositoryUrl}/pulls`} target="_blank" rel="noreferrer">
            Open candidates <ArrowUpRight size={15} />
          </a>
        </div>
      </section>
    </main>
  );
}
