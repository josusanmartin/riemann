import type { Metadata } from "next";
import Link from "next/link";
import { Download } from "lucide-react";
import { getCurrentRecord } from "@/lib/records";

export const metadata: Metadata = {
  title: "An unconditional 669/800 bound in Lean",
  description: "A reproducible composition of the published RH proof and the Zeta23 distinct-zero theorem. Includes source, build pins, and verification evidence.",
};

const evidence = "/evidence/critical-line-669";
const rhCommit = "2f097b744a6460c73f3e4cc550baa83698409876";

export default function CriticalLineResearchPage() {
  const current = getCurrentRecord();
  return (
    <main id="main-content">
      <section className="inner-hero shell-wrap">
        <div className="shell inner-hero-grid">
          <div>
            <span className="eyebrow">Research evidence · November 21, 2026</span>
            <h1>An unconditional 669/800 bound in Lean.</h1>
            <p>The formalization combines Alpöge’s published proof of the Riemann hypothesis with Alpöge and Furman’s lower bound for distinct zeros. Lean checks the resulting critical-line bound in both dyadic and cumulative intervals.</p>
            <a className="button button-lime" href={`${evidence}/critical-line-669-lean.zip`} download><Download size={17} /> Download source and build script</a>
          </div>
          <aside className="challenge-score-card">
            <span>Lean-checked research result</span>
            <strong>83.625%</strong>
            <code>669 / 800</code>
            <p>Official leaderboard replay pending</p>
          </aside>
        </div>
      </section>
      <section className="shell section-space contract-layout">
        <article className="prose-section">
          <h2>What the theorem proves</h2>
          <p>For every positive ε and all sufficiently large T, the number of distinct zeros on the critical line is at least (669/800 − ε) times the total zero count with multiplicity. This holds in both (T, 2T] and (0, T].</p>
          <p>The proof applies the imported theorem <code>riemannHypothesis</code> to identify distinct zeros with distinct critical-line zeros in every window. The final statements <code>dyadic_669</code> and <code>cumulative_669</code> have no RH premise. <a className="text-link" href={`${evidence}/CriticalLine669.lean`}>Read the Lean declarations</a></p>
          <h2>Verification and ranking</h2>
          <p>The joint build uses Lean 4.33.1, a pinned Mathlib revision and hash-checked RH build artifacts. The verification log records Lean kernel replay of both new modules and a fresh Zeta23 rebuild. The final declarations depend on <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. <a className="text-link" href={`${evidence}/verification.txt`}>Read the verification log</a></p>
          <p>The competition verifier pins Lean 4.33.0-rc2 and a different Mathlib revision. Ranking this result requires an official replay of the unconditional competition statements with Comparator, Lean and nanoda in a compatible environment. <Link className="text-link" href={`/submissions/${current.id}`}>Current ranked record</Link></p>
        </article>
        <aside className="toc-card">
          <h2>Proof dependencies</h2>
          <a href={`https://github.com/leanprover-community/riemann-hypothesis/tree/${rhCommit}`}>Published RH source and build cache</a>
          <a href="https://math.mit.edu/~drew/grh/">Independent checks of the RH proof</a>
          <a href="https://arxiv.org/abs/2608.13637">Alpöge–Furman distinct-zero bound</a>
          <h2>Earlier conditional replay</h2>
          <p>The earlier solution took RH as an argument. Comparator matched those conditional statements, and Lean and nanoda accepted them on Boat.</p>
          <a href="/rh-conditional/669-800.zip" download>Download the conditional replay</a>
          <a href="/rh-conditional/669-800.log">Read the Boat verifier log</a>
        </aside>
      </section>
    </main>
  );
}
