import { Braces, FileCheck2, GitPullRequestArrow, ShieldCheck, TrendingUp } from "lucide-react";

const steps = [
  { icon: GitPullRequestArrow, number: "01", title: "Open a PR", text: "Submit an exact rational score and Lean source. No uploads or opaque binaries." },
  { icon: Braces, number: "02", title: "Freeze the claim", text: "Trusted CI generates the theorem. Contributors cannot change the definitions or hypotheses." },
  { icon: FileCheck2, number: "03", title: "Replay the proof", text: "Comparator checks statement equality, the axiom set, and both dyadic and cumulative bounds." },
  { icon: ShieldCheck, number: "04", title: "Check two kernels", text: "Lean and nanoda independently accept the exported proof in a credential-free sandbox." },
  { icon: TrendingUp, number: "05", title: "Advance the record", text: "A separate trusted job merges and publishes only a strict exact improvement." },
];

export function VerificationPipeline() {
  return (
    <section className="pipeline-section" aria-labelledby="pipeline-title">
      <div className="section-heading pipeline-heading">
        <div><span className="eyebrow eyebrow-light">From code to theorem</span><h2 id="pipeline-title">The checker is the referee</h2></div>
        <p>No committee gates the formal leaderboard. Human review is a separate badge, never a substitute for a proof.</p>
      </div>
      <ol className="pipeline-grid">
        {steps.map(({ icon: Icon, number, title, text }) => (
          <li key={number}>
            <div className="pipeline-icon"><Icon size={22} /></div>
            <span>{number}</span><h3>{title}</h3><p>{text}</p>
          </li>
        ))}
      </ol>
    </section>
  );
}
