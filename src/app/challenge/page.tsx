import type { Metadata } from "next";
import Link from "next/link";
import {
  ArrowRight,
  Binary,
  Braces,
  Check,
  FileLock2,
  Scale,
} from "lucide-react";
import { CodeBlock } from "@/components/code-block";
import { contract, getCurrentRecord } from "@/lib/records";

export const metadata: Metadata = {
  title: "Challenge contract",
  description:
    "The fixed theorem, the scoring rule, and the trust boundary for the critical-line bound challenge.",
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
            <h1>Improve one constant in a fixed theorem.</h1>
            <p>
              Submit an exact rational κ with a Lean proof of the fixed unconditional
              asymptotic theorem. A submission is accepted when κ exceeds the current record.
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
          <span className="eyebrow">What is scored</span>
          <h2>A lower bound for distinct zeros on Re(s) = ½</h2>
          <p>
            Let <i>N</i> count nontrivial zeros of the Riemann zeta function with
            multiplicity, and let <i>N₀*</i> count distinct zeros on the critical
            line. Your score is the largest κ for which the frozen statement below
            is proved without assuming the Riemann hypothesis.
          </p>
          <CodeBlock label="Trusted statement · dyadic form">{theorem}</CodeBlock>
          <p>
            The build also requires the cumulative form, so a submission cannot
            change the displayed value by proving only a differently shaped
            statement.
          </p>
          <CodeBlock label="Trusted statement · cumulative form">{cumulativeTheorem}</CodeBlock>
        </article>

        <aside className="toc-card">
          <span className="toc-title">On this page</span>
          <a href="#score">How scoring works</a>
          <a href="#frozen">What is frozen</a>
          <a href="#accepted">What is accepted</a>
          <a href="#pins">Pinned foundation</a>
        </aside>
      </section>

      <section className="shell rule-section" id="score">
        <div className="section-heading split-heading">
          <div><span className="eyebrow">Scoring</span><h2>How scoring works</h2></div>
          <p>The percentage shown is for display only. The comparator uses exact terms and integer cross-multiplication.</p>
        </div>
        <div className="rule-grid">
          <article><div className="rule-icon"><Binary size={22} /></div><h3>Exact rational</h3><p>Submit positive decimal strings <code>p</code> and <code>q</code>. Floating-point input is never accepted.</p></article>
          <article><div className="rule-icon"><Scale size={22} /></div><h3>Strict comparison</h3><p>Lean proves <code>currentRecordKappa &lt; candidateKappa</code> inside the same formal environment.</p></article>
          <article><div className="rule-icon"><Braces size={22} /></div><h3>Same theorem</h3><p>Comparator checks exact statement equality before either kernel is allowed to certify the result.</p></article>
        </div>
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
          <div><dt>Mathlib</dt><dd>{contract.trustedUpstream.mathlibCommit.slice(0, 12)}</dd></div>
          <div><dt>Comparator</dt><dd>{contract.verifier.comparatorCommit.slice(0, 12)}</dd></div>
          <div><dt>nanoda</dt><dd>{contract.verifier.nanodaCommit.slice(0, 12)}</dd></div>
        </dl>
        <Link className="text-link" href="/methodology">See the complete trust model <ArrowRight size={16} /></Link>
      </section>
    </main>
  );
}
