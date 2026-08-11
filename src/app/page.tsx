import Link from "next/link";
import { ArrowRight, BadgeCheck, CircleDot, Github, LockKeyhole, Sigma } from "lucide-react";
import { ZetaField } from "@/components/zeta-field";
import { BoundChart } from "@/components/bound-chart";
import { Leaderboard } from "@/components/leaderboard";
import { VerificationPipeline } from "@/components/verification-pipeline";
import { contract, getCurrentRecord, getRecords } from "@/lib/records";
import { repository, repositoryUrl, siteUrl } from "@/lib/site";
import { truncateDecimalString } from "@/components/format";
import { CodeBlock } from "@/components/code-block";

export default function Home() {
  const current = getCurrentRecord();
  const history = getRecords();
  const repoName = repository.split("/").at(-1) ?? "riemann";
  const quickstart = `git clone ${repositoryUrl}.git
cd ${repoName} && npm install

# add submissions/<name>/submission.json + proof/Solution.lean
npx tsx scripts/verify-submission.ts submissions/<name> --mode=quick

# then upload proof/Solution.lean at ${siteUrl}/submit`;
  // The starting point for this arena is the Anthropic paper; improvement is
  // measured against that fixed baseline, so it reads 0 until a record beats it.
  const currentPercent = Number(current.scorePercent);
  const baselinePercent = Number(contract.baseline.percent);
  const improvement = currentPercent - baselinePercent;

  return (
    <main id="main-content">
      <section className="hero shell-wrap">
        <div className="shell hero-panel">
          <ZetaField />
          <div className="hero-content">
            <div className="status-pill"><span className="pulse-dot" /> Open for submissions <span>·</span> Verified in Lean</div>
            <h1>The largest <em>proven</em> proportion of zeros on the critical line.</h1>
            <p className="hero-lede">This site records the current unconditional lower bound on the fraction of nontrivial Riemann zeta zeros that lie on the critical line. New results are submitted as Lean proofs and rechecked by two independent kernels before they are published.</p>
            <div className="hero-actions">
              <Link className="button button-lime" href="/submit">Submit a result <ArrowRight size={17} /></Link>
              <a className="button button-ghost-light" href={repositoryUrl} target="_blank" rel="noreferrer"><Github size={17} /> View source</a>
            </div>
          </div>

          <div className="record-display">
            <div className="record-label"><BadgeCheck size={17} /> Current kernel-verified record</div>
            <div className="record-number"><span>{truncateDecimalString(current.scorePercent, 10)}</span><sup>%</sup></div>
            <code>κ₀ = {current.exactExpression}</code>
            <div className="frontier-progress">
              <div className="progress-labels"><span>Certified fraction</span><strong>{truncateDecimalString(current.scorePercent, 4)} / 100</strong></div>
              <div className="progress-track" role="meter" aria-label="Certified critical-line proportion" aria-valuenow={currentPercent} aria-valuemin={0} aria-valuemax={100} aria-valuetext={`${truncateDecimalString(current.scorePercent, 4)} percent of nontrivial zeros certified`}>
                <span className="prior-marker" style={{ left: `${baselinePercent}%` }} aria-hidden="true" />
                <span className="progress-fill" style={{ width: `${currentPercent}%` }} />
              </div>
              <div className="progress-scale"><span>0%</span><span>Previous {truncateDecimalString(contract.baseline.percent, 2)}%</span><span>100%</span></div>
            </div>
          </div>

          <div className="hero-metrics">
            <div><span>Increase</span><strong>+{improvement.toFixed(2)}<small> pts</small></strong><p>over the Anthropic 2026 starting record</p></div>
            <div><span>Verification</span><strong>2<small> kernels</small></strong><p>the Lean kernel and an independent nanoda replay</p></div>
            <div><span>Assumptions</span><strong>0</strong><p>the result does not assume the Riemann hypothesis</p></div>
          </div>
        </div>
      </section>

      <section className="shell section-space intro-grid">
        <div className="intro-copy">
          <span className="eyebrow">How the score is defined</span>
          <h2>A single number, compared exactly.</h2>
        </div>
        <div className="intro-text">
          <p>The score κ is the proven lower bound for the count of distinct nontrivial zeros on the critical line, divided by all nontrivial zeros counted with multiplicity. A larger κ is a stronger unconditional result.</p>
          <p>Each candidate is an exact rational. Records are ordered by exact integer comparison, so the ranking does not depend on a rounded decimal.</p>
        </div>
      </section>

      <section className="shell chart-section">
        <BoundChart records={history} />
      </section>

      <section className="shell section-space">
        <Leaderboard records={history} />
      </section>

      <section className="shell section-space participate">
        <div className="participate-intro">
          <span className="eyebrow">Participate</span>
          <h2>Submit from the site, or run the verifier yourself.</h2>
          <p>Sign in and upload a Lean proof, or clone the repository and check it locally. A coding agent can drive the whole loop.</p>
        </div>
        <div className="participate-paths">
          <div className="participate-card">
            <h3>From the site</h3>
            <p>Sign in with GitHub, then paste an exact bound and its Lean proof. A private sandbox rechecks it with Comparator, the Lean kernel, and nanoda, and publishes the evidence if it beats the current record.</p>
            <Link className="button button-lime" href="/submit">Submit a result <ArrowRight size={16} /></Link>
          </div>
          <div className="participate-card">
            <h3>Locally, or with a coding agent</h3>
            <CodeBlock label="terminal">{quickstart}</CodeBlock>
            <p className="participate-note">Point a coding agent at the repository and its <code>CONTRIBUTING.md</code> to run clone → improve → verify. Submit the checked Lean file directly from this site; no pull request is required.</p>
          </div>
        </div>
      </section>

      <section className="dark-section">
        <div className="shell"><VerificationPipeline /></div>
      </section>

      <section className="shell section-space contract-grid">
        <div className="contract-copy">
          <span className="eyebrow">How scoring works</span>
          <h2>Each submission is a Lean proof of a fixed theorem.</h2>
          <p>The build inserts the candidate value into a fixed statement. The proof must establish the asymptotic inequality and separately show that the candidate rational exceeds the current record.</p>
          <Link className="text-link" href="/challenge">Read the full challenge contract <ArrowRight size={16} /></Link>
        </div>
        <div className="theorem-card">
          <div className="theorem-top"><Sigma size={18} /><span>candidate_critical_line_bound</span><span className="locked"><LockKeyhole size={13} /> Locked</span></div>
          <div className="theorem-body">
            <p className="theorem-math">∀ ε &gt; 0, ∃ T₀, ∀ T ≥ T₀,</p>
            <p className="theorem-main">(κ − ε) · N(T, 2T) ≤ N₀*(T, 2T)</p>
            <div className="theorem-defs"><span><i>N</i> counts with multiplicity</span><span><i>N₀*</i> counts distinct zeros on Re(s)=½</span></div>
          </div>
          <div className="theorem-bottom"><CircleDot size={14} /> The only candidate-controlled value is κ = p/q</div>
        </div>
      </section>

      <section className="shell final-cta">
        <div>
          <span className="eyebrow eyebrow-light">Submissions</span>
          <h2>Submit a new lower bound.</h2>
          <p>A result is published once its exact theorem passes both kernels.</p>
        </div>
        <div className="final-actions">
          <Link className="button button-lime" href="/submit">Submit a result <ArrowRight size={17} /></Link>
          <Link className="button button-ghost-light" href="/methodology">Read the verification method</Link>
        </div>
      </section>
    </main>
  );
}
