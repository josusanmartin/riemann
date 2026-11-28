import type { Metadata } from "next";
import Link from "next/link";
import { truncateDecimalString } from "@/components/format";
import { competitions } from "@/lib/competitions";
import { competitionTrackSchema } from "@/lib/challenge";
import { getRecords } from "@/lib/records";
import styles from "./challenges.module.css";

export const metadata: Metadata = { title: "Challenges", description: "Explore the distinct-zero and simple-zero competitions and open formalization problems." };

export default function Challenges() {
  return <main id="main-content" className={`shell section-space ${styles.directory}`}>
    <h1>Challenges</h1>
    <p className={styles.lede}>One leaderboard counts distinct zero locations on the critical line. The other counts zeros of multiplicity one. Choose a board to see its records and submit a proof.</p>
    <div className={styles.boards}>
      {competitionTrackSchema.options.map(track => {
        const item = competitions[track];
        const current = getRecords(track).filter(record => record.status === "kernel-verified").at(-1);
        return <article key={track}>
          <h2>{item.title}</h2><p>{item.description}</p>
          <strong>{current ? truncateDecimalString(current.scorePercent, 6) + "%" : "Open for a first record"}</strong>
          <small>{current ? "Current verified lower bound" : "Opening threshold · strictly above ⅔"}</small>
          <div className={styles.cardLinks}>
            <Link href={item.board} className="text-link">{item.shortTitle} leaderboard →</Link>
            {item.rules !== item.board && <Link href={item.rules} className="text-link">Rules</Link>}
          </div>
        </article>;
      })}
    </div>
    <h2>Formalization problems</h2>
    <p>Reproduce a specific theorem from the literature in Lean.</p>
    <Link className="text-link" href="/challenges/simple-zeros/xu">Yuanda Xu’s 71.27406684% simple-zero theorem →</Link>
  </main>;
}
