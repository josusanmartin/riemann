import type { Metadata } from "next";
import Link from "next/link";
import { ArrowRight, BadgeCheck, BookOpen, UploadCloud, UserCheck } from "lucide-react";
import { getRecords } from "@/lib/records";
import { truncateDecimalString } from "@/components/format";

export const metadata: Metadata = {
  title: "Submissions",
  description:
    "Every accepted critical-line record, newest first, with immutable proof evidence.",
};

export default function SubmissionsIndexPage() {
  const records = [...getRecords()].reverse();

  return (
    <main id="main-content">
      <section className="shell section-space submissions-index">
        <span className="eyebrow">Record ledger</span>
        <h1>Every accepted record</h1>
        <p className="submissions-lede">
          Newest first. Each entry links to its evidence; values are truncated,
          never rounded up. Uploads remain private while verification runs and
          become public only when both kernels accept a strict improvement.
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
                <span className="submissions-badges">
                  <span className={record.formalVerification ? "submissions-badge verified" : "submissions-badge"}>
                    {record.formalVerification ? <BadgeCheck size={15} /> : <BookOpen size={15} />}
                    {record.formalVerification ? "Kernel" : "Paper"}
                  </span>
                  {record.independentReview && (
                    <span className="submissions-badge expert"><UserCheck size={15} /> Expert</span>
                  )}
                </span>
              </Link>
            </li>
          ))}
        </ol>
        <div className="submissions-open">
          <UploadCloud size={20} />
          <p>
            <strong>Working on a candidate?</strong> Submit one Lean file directly;
            no repository fork or pull request is required.
          </p>
          <Link className="button button-dark" href="/submit">
            Submit a proof <ArrowRight size={15} />
          </Link>
        </div>
      </section>
    </main>
  );
}
