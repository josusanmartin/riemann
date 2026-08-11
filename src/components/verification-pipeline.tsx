import { Braces, FileCheck2, ShieldCheck, TrendingUp, UploadCloud } from "lucide-react";

const steps = [
  { icon: UploadCloud, number: "01", title: "Upload one Lean file", text: "Sign in with GitHub and submit an exact rational score plus plain Lean source." },
  { icon: Braces, number: "02", title: "Fix the statement", text: "The build generates the theorem from trusted templates. A submission cannot change the definitions or hypotheses." },
  { icon: FileCheck2, number: "03", title: "Recheck the proof", text: "Comparator checks statement equality, the axiom set, and both the dyadic and cumulative bounds." },
  { icon: ShieldCheck, number: "04", title: "Replay in two kernels", text: "The Lean kernel and nanoda independently accept the exported proof in a credential-free sandbox." },
  { icon: TrendingUp, number: "05", title: "Publish the record", text: "A separate trusted service archives the exact source and atomically publishes only a strict improvement." },
];

export function VerificationPipeline() {
  return (
    <section className="pipeline-section" aria-labelledby="pipeline-title">
      <div className="section-heading pipeline-heading">
        <div><span className="eyebrow eyebrow-light">How verification works</span><h2 id="pipeline-title">How a submission is checked</h2></div>
        <p>A durable FIFO runs one proof at a time, with three uploads per GitHub account each UTC day. Acceptance depends only on the automated check; expert review is recorded separately.</p>
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
