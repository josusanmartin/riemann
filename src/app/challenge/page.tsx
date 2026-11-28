import { verificationDuration, workerDuration } from "@/lib/verification-duration";
import nanodaRelease from "../../../boat/compact/nanoda-release.json";
import type { Metadata } from "next";
import Link from "next/link";
import {
  ArrowRight,
  Check,
  FileLock2,
} from "lucide-react";
import { CodeBlock } from "@/components/code-block";
import { contract, getCurrentRecord } from "@/lib/records";

export const metadata: Metadata = {
  title: "Competition rules",
  description:
    "Scoring, required Lean declarations, sandbox limits and verification for the distinct critical-line zero challenge.",
};

const theorem = `theorem candidate_critical_line_bound :
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (candidateKappa - ε) * (Ncount T (2 * T) : ℝ)
      ≤ N0star T (2 * T)`;

const cumulativeTheorem = `theorem candidate_critical_line_bound_cumulative :
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (candidateKappa - ε) * (Ncount 0 T : ℝ)
      ≤ N0star 0 T`;

export default function ChallengePage() {
  const current = getCurrentRecord();

  return (
    <main id="main-content">
      <section className="inner-hero shell-wrap">
        <div className="shell inner-hero-grid">
          <div>
            <span className="eyebrow">Critical-line bound</span>
            <h1>Competition rules</h1>
            <p>
              Prove a larger lower bound for the proportion of distinct zeros on the critical line. The same score must hold in both height intervals.
            </p>
            <Link className="button button-lime" href="/submit">
              Start a submission <ArrowRight size={17} />
            </Link>
          </div>
          <aside className="challenge-score-card" aria-label="Current score to beat">
            <span>Current record</span>
            <strong>{current.scoreDecimal}…</strong>
            <code>{current.exactExpression}</code>
            <p>A new submission must be strictly greater; equality does not qualify.</p>
          </aside>
        </div>
      </section>

      <section className="shell section-space contract-layout">
        <article className="prose-section">
          <h2 id="score">How to earn a record</h2>
          <ol className="competition-rules">
            <li><strong>Count each location once.</strong> The numerator counts distinct nontrivial zeros on Re(s) = ½. The denominator counts all nontrivial zeros with multiplicity. A double zero on the line adds one to the numerator and two to the denominator.</li>
            <li><strong>Beat the current bound.</strong> Submit κ = p/q with positive integers p and q and κ ≤ 1. Lean must prove that κ strictly exceeds the current exact record. The displayed percentage is truncated.</li>
            <li><strong>Prove the same κ in both intervals.</strong> For every ε &gt; 0 and all sufficiently large T, the proportion must be at least κ − ε in (T, 2T] and in (0, T]. The first counts zeros between heights T and 2T. The second counts all zeros up to height T.</li>
            <li><strong>Use the pinned foundation.</strong> The verifier links the compact proof of RH into the certificate. Further mathematical inputs need proofs in the pinned environment. The permitted axioms are <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. You may reuse proved lemmas from its libraries.</li>
            <li><strong>Supply all three declarations.</strong> Your single Lean file must prove strict improvement, the dyadic bound, and the cumulative bound with the signatures in the starter. You may derive the cumulative result from the dyadic one in that file.</li>
            <li><strong>Pass official replay.</strong> Comparator matches the statements and checks the axiom dependencies. Lean and nanoda must both accept the exported proof before the score enters the leaderboard.</li>
          </ol>

          <h2 id="baseline">Why the board started at 67.25%</h2>
          <p>Anthropic’s Zeta23 development proved two bounds without assuming RH. At least 67.25007% of zeros are simple and on the critical line. Each of those zeros counts once toward this challenge, so the original board used that figure as its baseline.</p>
          <p>The same development proved that at least 83.625035% of zeros are distinct across the whole critical strip. When the board adopted RH as a premise, all those distinct locations could be counted on the line. The first record using that premise certified the rational bound 669/800, or 83.625%. <a className="text-link" href="https://github.com/anthropics/formal-math/blob/3635e74826a4c1fcece7d1cd2b6fa75e43a00510/Zeta23/ThmD/Mult.lean#L435-L480">Zeta23 theorems</a> · <Link className="text-link" href="/submissions/critical-line-669-800">First RH-based record</Link></p>

          <h2 id="meaning">What would 100% mean?</h2>
          <p>RH puts every nontrivial zero on the critical line. A score of 100% would also prove that almost all zeros are simple. The fraction of zero occurrences at multiple zeros tends to zero. Rare multiple zeros are compatible with that limit.</p>
          <p>Section 7.3 of Anthropic’s paper gives a written RH-based lower bound of about 85.082% for distinct zeros, using a third-moment estimate and the 19/27 simple-zero bound. A leaderboard entry at that level needs a complete Lean deduction for both intervals. <a className="text-link" href="https://assets.claude.com/95c246936988e43127bc6b2ceb7077c1dad2d68e.pdf#page=14">Read §7.3</a></p>

          <h2 id="statements">Required bounds</h2>
          <CodeBlock label="Trusted statement · dyadic form">{theorem}</CodeBlock>
          <CodeBlock label="Trusted statement · cumulative form">{cumulativeTheorem}</CodeBlock>
        </article>

        <aside className="toc-card">
          <span className="toc-title">On this page</span>
          <Link href="/challenges">All challenges</Link>
          <a href="#score">How to earn a record</a>
          <a href="#baseline">Why 67.25% was the baseline</a>
          <a href="#meaning">What 100% means</a>
          <a href="#statements">Required bounds</a>
          <a href="#sandbox">Sandbox and upload limits</a>
          <a href="#frozen">What is frozen</a>
          <a href="#accepted">What is accepted</a>
          <a href="#pins">Pinned foundation</a>
        </aside>
      </section>

      <section className="shell rule-section" id="sandbox" aria-labelledby="sandbox-title">
        <div className="section-heading split-heading">
          <div><h2 id="sandbox-title">Sandbox and upload limits</h2></div>
          <p>Each competitive proof runs in an isolated Boat worker. A timeout or memory failure leaves the proposed bound unverified.</p>
        </div>
        <dl className="sandbox-limits">
          <div><dt>Source and dependencies</dt><dd>One UTF-8 <code>Solution.lean</code>, up to 2,000,000 bytes. The entire encoded API request may use up to 4,000,000 bytes. Imports must be available in the pinned environment.</dd></div>
          <div><dt>Memory and retry</dt><dd>The standard worker has 16 GB of RAM and a 12 GiB verifier cap. A kernel-confirmed out-of-memory kill triggers one retry on a 32 GB worker with a 28 GiB cap. It keeps the same proof, queue position and daily slot. A timeout or proof error ends the attempt.</dd></div>
          <div><dt>Time</dt><dd>Each attempt has {verificationDuration} in total for proof compilation, export and kernel checks. Queue time is separate. The site retries worker assignment and proof transfer within a three-minute setup window. The VM stops when the job finishes and has a maximum lifetime of {workerDuration}.</dd></div>
          <div><dt>Processes and files</dt><dd>Lean is configured for two threads. The isolated check allows up to 512 tasks (processes and threads) and limits each file it writes to 8 GiB.</dd></div>
          <div><dt>Isolation</dt><dd>Proof code runs as an unprivileged user without network access or publishing credentials. The verifier, toolchain and staged inputs are read-only to that user. Dependencies are prepared before the proof runs.</dd></div>
          <div><dt>Queue and publication</dt><dd>One job runs at a time in admission order. Each GitHub account gets five admissions per UTC day, resetting at 00:00 UTC. Every admitted upload is archived privately, including failed attempts. Accepted proofs are published under Apache-2.0.</dd></div>
        </dl>
      </section>

      <section className="frozen-section" id="frozen">
        <div className="shell frozen-grid">
          <div>
            <span className="eyebrow eyebrow-light">Fixed by the challenge</span>
            <h2>A submission controls only the proof and κ.</h2>
            <p>The server accepts only one Lean source file, then the isolated verifier regenerates the target from root-owned templates.</p>
          </div>
          <ul className="check-list check-list-dark">
            <li><Check size={17} /> Definitions of <i>N</i>, <i>N₀*</i>, and the critical line</li>
            <li><Check size={17} /> Quantifier order, asymptotic window, and hypotheses</li>
            <li><Check size={17} /> Current exact record and strict comparison</li>
            <li><Check size={17} /> Toolchain, Mathlib tree, kernels, and axiom allowlist</li>
            <li><Check size={17} /> Verifier scripts and promotion workflow</li>
          </ul>
        </div>
      </section>

      <section className="shell section-space" id="accepted">
        <div className="section-heading split-heading">
          <div><span className="eyebrow">Acceptance boundary</span><h2>Formal record, or supporting evidence</h2></div>
          <p>Only a complete formal submission changes the record.</p>
        </div>
        <div className="acceptance-grid">
          <article className="acceptance-card accepted">
            <span className="acceptance-kicker"><Check size={15} /> Advances the record</span>
            <h3>Complete formal submission</h3>
            <p>An authenticated Lean upload whose generated statements, permitted axioms, and exported proof pass Lean and nanoda.</p>
          </article>
          <article className="acceptance-card">
            <span className="acceptance-kicker"><FileLock2 size={15} /> Does not advance it</span>
            <h3>Paper, computation, or partial proof</h3>
            <p>Open an issue to share the idea. Numerical evidence and expert review can guide the work but cannot certify κ.</p>
          </article>
        </div>
      </section>

      <section className="shell pins-card" id="pins">
        <div><span className="eyebrow">Pinned dependencies</span><h2>Every dependency is pinned by commit.</h2></div>
        <dl className="pin-list">
          <div><dt>Zeta23</dt><dd>{contract.trustedUpstream.commit.slice(0, 12)}</dd></div>
          <div><dt>Lean</dt><dd>{contract.trustedUpstream.leanToolchain}</dd></div>
          <div><dt>Accepted RH proof</dt><dd><a href={`https://github.com/${contract.trustedUpstream.rh.repository}/tree/${contract.trustedUpstream.rh.commit}`}>{contract.trustedUpstream.rh.commit.slice(0,12)}</a></dd></div>
          <div><dt>Mathlib</dt><dd>{contract.trustedUpstream.mathlibCommit.slice(0, 12)}</dd></div>
          <div><dt>Comparator and Lean kernel</dt><dd><a href={`https://github.com/leanprover/lean4/tree/${contract.verifier.leanReleaseCommit}`}>Lean release {contract.verifier.leanReleaseCommit.slice(0, 12)}</a></dd></div>
          <div><dt>Independent kernel</dt><dd><a href={`https://github.com/ammkrn/nanoda_lib/tree/${nanodaRelease.revision}`}>nanoda {nanodaRelease.version}</a></dd></div>
        </dl>
        <Link className="text-link" href="/methodology">See the complete trust model <ArrowRight size={16} /></Link>
      </section>
    </main>
  );
}
