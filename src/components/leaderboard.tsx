import Link from "next/link";
import { ArrowUpRight, BadgeCheck, BookOpen, UserCheck } from "lucide-react";
import type { RecordEntry } from "@/lib/challenge";
import { truncateDecimalString } from "@/components/format";

export function Leaderboard({ records }: { records: RecordEntry[] }) {
  const ranked = [...records].reverse();
  return (
    <section className="leaderboard-card" id="leaderboard" aria-labelledby="leaderboard-title">
      <div className="section-heading leaderboard-heading">
        <div>
          <span className="eyebrow">Unconditional lower bounds</span>
          <h2 id="leaderboard-title">Record ledger</h2>
        </div>
        <div className="legend"><span className="legend-dot" /> Higher is better</div>
      </div>
      <p className="table-scroll-hint" aria-hidden="true">Swipe sideways for method and evidence →</p>
      <div className="table-scroll">
        <table>
          <thead>
            <tr><th>Rank</th><th>Bound</th><th>Result</th><th>Method</th><th>Evidence</th></tr>
          </thead>
          <tbody>
            {ranked.map((record, index) => (
              <tr key={record.id} className={index === 0 ? "current-row" : undefined}>
                <td><span className="rank">{String(index + 1).padStart(2, "0")}</span></td>
                <td>
                  <Link href={`/submissions/${record.id}`} className="score-cell">
                    <strong>{truncateDecimalString(record.scorePercent, index === 0 ? 10 : 4)}%</strong>
                    {index === 0 && <span className="record-chip">Current</span>}
                  </Link>
                </td>
                <td><strong>{record.author}</strong><small>{record.date.slice(0, 4)} · {record.title}</small></td>
                <td><span className="method-cell">{record.method}</span></td>
                <td>
                  <div className="evidence-links">
                    <a className="evidence-link" href={record.proofUrl ?? record.sourceUrl} target="_blank" rel="noreferrer">
                      {record.formalVerification ? <BadgeCheck size={17} /> : <BookOpen size={17} />}
                      {record.formalVerification ? "Kernel" : "Paper"}
                      <ArrowUpRight size={13} />
                    </a>
                    {record.independentReview && (
                      <a className="evidence-link expert" href={record.independentReview.url} target="_blank" rel="noreferrer">
                        <UserCheck size={17} /> Expert <ArrowUpRight size={13} />
                      </a>
                    )}
                  </div>
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </section>
  );
}
