import type { Metadata } from "next";
import Link from "next/link";
import { truncateDecimalString } from "@/components/format";
import { getCurrentRecord, getRecords } from "@/lib/records";
import styles from "./challenges.module.css";

export const metadata: Metadata = { title: "Challenges", description: "Explore the distinct-zero and simple-zero competitions and open formalization problems." };

export default function Challenges() {
  const distinct = getCurrentRecord();
  const simple = getRecords("simple-zeros").at(-1);
  return <main id="main-content" className={`shell section-space ${styles.directory}`}>
    <h1>Challenges</h1>
    <p className={styles.lede}>One leaderboard counts distinct zero locations on the critical line. The other counts zeros of multiplicity one. Choose a board to see its records and submit a proof.</p>
    <div className={styles.boards}>
      <article>
        <h2>Distinct zeros on the critical line</h2>
        <p>Count each location on the line once, including locations where several zeros coincide.</p>
        <strong>{truncateDecimalString(distinct.scorePercent, 6)}%</strong><small>Current verified lower bound</small>
        <Link href="/#leaderboard" className="text-link">Distinct-zero leaderboard →</Link>
        <Link href="/challenge" className="text-link">Rules</Link>
      </article>
      <article>
        <h2>Simple zeros</h2>
        <p>Count only zeros of multiplicity one. A double zero contributes zero to this count.</p>
        <strong>{simple ? truncateDecimalString(simple.scorePercent, 6) + "%" : "Open for a first record"}</strong>
        <small>{simple ? "Current verified lower bound" : "Opening threshold · strictly above ⅔"}</small>
        <Link href="/challenges/simple-zeros" className="text-link">Simple-zero leaderboard and rules →</Link>
      </article>
    </div>
    <h2>Formalization problems</h2>
    <p>Reproduce a specific theorem from the literature in Lean.</p>
    <Link className="text-link" href="/challenges/simple-zeros/xu">Yuanda Xu’s 71.27406684% simple-zero theorem →</Link>
  </main>;
}
