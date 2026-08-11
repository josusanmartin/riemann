import Link from "next/link";
import { ArrowRight, BadgeCheck, CircleDot, Github, LockKeyhole, Sigma } from "lucide-react";
import { ZetaField } from "@/components/zeta-field";
import { BoundChart } from "@/components/bound-chart";
import { Leaderboard } from "@/components/leaderboard";
import { VerificationPipeline } from "@/components/verification-pipeline";
import { getCurrentRecord, getRecords } from "@/lib/records";
import { repositoryUrl } from "@/lib/site";
import { truncateDecimalString } from "@/components/format";

export default function Home() {
  const current = getCurrentRecord();
  const history = getRecords();
  const prior = history.at(-2);
  const currentPercent = Number(current.scorePercent);
  const priorPercent = Number(prior?.scorePercent ?? "0");
  const improvement = currentPercent - priorPercent;

  return (
    <main id="main-content">
      <section className="hero shell-wrap">
        <div className="shell hero-panel">
          <ZetaField />
          <div className="hero-content">
            <div className="status-pill"><span className="pulse-dot" /> Open formal challenge <span>·</span> Higher is better</div>
            <h1>The bound only moves<br />when the <em>proof</em> checks.</h1>
            <p className="hero-lede">Improve the unconditional proportion of Riemann zeta zeros proved to lie on the critical line. Submit Lean code; two kernels decide.</p>
            <div className="hero-actions">
              <Link className="button button-lime" href="/submit">Enter the challenge <ArrowRight size={17} /></Link>
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
                <span className="prior-marker" style={{ left: `${priorPercent}%` }} aria-hidden="true" />
                <span className="progress-fill" style={{ width: `${currentPercent}%` }} />
              </div>
              <div className="progress-scale"><span>0%</span><span>Previous {prior ? truncateDecimalString(prior.scorePercent, 2) : "0"}%</span><span>100%</span></div>
            </div>
          </div>

          <div className="hero-metrics">
            <div><span>Record jump</span><strong>+{improvement.toFixed(2)}<small> pts</small></strong><p>over the previous published bound</p></div>
            <div><span>Verification</span><strong>2<small> kernels</small></strong><p>Lean plus independent nanoda replay</p></div>
            <div><span>RH hypotheses</span><strong>0<small> assumptions</small></strong><p>the theorem remains unconditional</p></div>
          </div>
        </div>
      </section>

      <section className="shell section-space intro-grid">
        <div className="intro-copy">
          <span className="eyebrow">One scalar. One frozen contract.</span>
          <h2>A mathematical record you can compare exactly.</h2>
        </div>
        <div className="intro-text">
          <p>The score κ is the certified lower bound for distinct nontrivial zeros on the critical line, divided by all nontrivial zeros counted with multiplicity. A larger κ is a stronger unconditional theorem.</p>
          <p>Every candidate is an exact rational. No benchmark noise, rounded comparisons, secret tests, or judgment calls can move the number.</p>
        </div>
      </section>

      <section className="shell chart-section">
        <BoundChart records={history} />
      </section>

      <section className="shell section-space">
        <Leaderboard records={history} />
      </section>

      <section className="dark-section">
        <div className="shell"><VerificationPipeline /></div>
      </section>

      <section className="shell section-space contract-grid">
        <div className="contract-copy">
          <span className="eyebrow">Immutable scoring law</span>
          <h2>Not a numerical experiment.<br />A theorem with a number in it.</h2>
          <p>CI writes the candidate value into a trusted statement. Your proof must establish the asymptotic inequality and separately prove that its exact rational is above the current exact record.</p>
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
          <span className="eyebrow eyebrow-light">The frontier is open</span>
          <h2>Can you move the seventh decimal?</h2>
          <p>A result advances the instant the exact theorem survives both kernels.</p>
        </div>
        <div className="final-actions">
          <Link className="button button-lime" href="/submit">Prepare a submission <ArrowRight size={17} /></Link>
          <Link className="button button-ghost-light" href="/methodology">Inspect the verifier</Link>
        </div>
      </section>
    </main>
  );
}
