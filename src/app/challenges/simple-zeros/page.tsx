import type { Metadata } from "next";
import Link from "next/link";
import { getRecords } from "@/lib/records";
import { Leaderboard } from "@/components/leaderboard";
import styles from "../challenges.module.css";

export const metadata: Metadata = { title: "Simple-zero leaderboard", description: "Prove lower bounds for zeros of multiplicity one in both height intervals." };

export default function SimpleZeros() {
  const records = getRecords("simple-zeros");
  return <main id="main-content" className={`shell section-space ${styles.directory}`}>
    <Link href="/challenges" className="text-link">← All challenges</Link>
    <h1>Simple zeros</h1>
    <p className={styles.lede}>Prove that a larger proportion of the nontrivial zeros of ζ have multiplicity one. Count every zero with multiplicity in the denominator.</p>
    <div className={styles.actions}>
      <Link className="button button-dark" href="/submit?track=simple-zeros">Submit a ranked proof</Link>
      <a className="text-link" href="/templates/Simple.lean" download>Download the Lean starter</a>
    </div>
    {records.length ? <Leaderboard records={records} /> : <section id="leaderboard"><h2>Leaderboard</h2><p>The first record is open. Submit an exact rational above ⅔ and prove it in both intervals. Accepted entries appear here after Lean and nanoda replay the proof.</p></section>}
    <section><h2>What earns a record?</h2>
      <p>For every ε &gt; 0, prove that the fraction of simple zeros is at least κ − ε for all sufficiently large T, both in (T, 2T] and in (0, T]. Use Zeta23’s <code>Nsimple</code> and <code>Ncount</code>. A zero of multiplicity three contributes zero to the numerator and three to the denominator.</p>
      <p>The first submission must beat ⅔. Each subsequent submission must beat the last verified simple-zero record. The pinned RH proof, axiom policy and shared five-upload daily allowance apply to both leaderboards. <Link className="text-link" href="/challenge#sandbox">Sandbox limits</Link></p>
    </section>
    <section><h2>Formalize Xu’s theorem</h2>
      <p>Xu’s Theorem 1 gives a cumulative lower bound of 71.27406684% under RH. You can submit a Lean formalization of that theorem on its own.</p>
      <Link className="text-link" href="/challenges/simple-zeros/xu">See the fixed theorem and submit a project →</Link>
    </section>
  </main>;
}
