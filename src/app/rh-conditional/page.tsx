import type { Metadata } from "next";
import Link from "next/link";
import { ArrowRight, Download } from "lucide-react";
import { repositoryUrl } from "@/lib/site";

export const metadata: Metadata = {
  title: "RH-conditional track",
  description: "Machine-checked lower bounds for distinct critical-line zeros assuming the Riemann hypothesis.",
};

export default function RhConditionalPage() {
  return (
    <main id="main-content">
      <section className="inner-hero shell-wrap">
        <div className="shell inner-hero-grid">
          <div>
            <span className="eyebrow">RH-conditional track</span>
            <h1>Critical-line bounds assuming RH.</h1>
            <p>Each counting theorem takes the Riemann hypothesis as an explicit argument. The score counts distinct zeros on the critical line and divides by the total number of zeros counted with multiplicity.</p>
            <a className="button button-lime" href={`${repositoryUrl}/issues/new?template=rh-conditional.yml`}>Submit a conditional proof <ArrowRight size={17} /></a>
          </div>
          <aside className="challenge-score-card">
            <span>Verified bound under RH</span>
            <strong>83.625%</strong>
            <code>669 / 800</code>
            <p>Verified on Boat · November 21, 2026</p>
          </aside>
        </div>
      </section>
      <section className="shell section-space contract-layout">
        <article className="prose-section">
          <h2>669/800 under the Riemann hypothesis</h2>
          <p>RH places every nontrivial zero on the critical line. A lower bound for distinct zeros anywhere in the strip therefore applies to distinct zeros on the line. The proof uses the Montgomery–Taylor bound in Zeta23 and an exact rational comparison.</p>
          <p>For every positive ε, both (T, 2T] and (0, T] eventually have a proportion of at least 669/800 − ε. Comparator matched the conditional statements. Lean and nanoda independently accepted the solution.</p>
          <a className="button button-dark" href="/rh-conditional/669-800.zip" download><Download size={16} /> Download replay and Lean source</a>
          <p><a className="text-link" href="/rh-conditional/669-800.log">Read the verifier log</a></p>
        </article>
        <aside className="toc-card">
          <h2>Submit an improvement</h2>
          <p>Choose an exact fraction above 669/800 and at most 1. Keep the three declaration signatures in the starter and replace each proof placeholder.</p>
          <a className="text-link" href="/rh-conditional/Solution.lean" download>Download the Lean starter</a>
          <p>Submit a public source link for maintainer replay. Multi-file projects and dependencies larger than 2 MB can be linked by commit or archive digest.</p>
          <Link className="text-link" href="/challenge">Unconditional track rules</Link>
        </aside>
      </section>
    </main>
  );
}
