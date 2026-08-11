import type { Metadata } from "next";
import Link from "next/link";
import {
  ArrowRight,
  Box,
  CheckCircle2,
  FileSearch,
  GitPullRequestArrow,
  KeyRound,
  Network,
  ShieldCheck,
} from "lucide-react";
import { CodeBlock } from "@/components/code-block";
import { VerificationPipeline } from "@/components/verification-pipeline";
import { contract } from "@/lib/records";

export const metadata: Metadata = {
  title: "Verification methodology",
  description:
    "How Riemann.fail isolates untrusted Lean code, compares exact statements, replays two kernels, and promotes records.",
};

const command = `npm ci
tools_dir="$(mktemp -d)"
bash scripts/install-verifier-tools.sh "$tools_dir"
export COMPARATOR_BIN="$tools_dir/comparator/.lake/build/bin/comparator"
export COMPARATOR_LANDRUN="$tools_dir/landrun/landrun"
export COMPARATOR_LEAN4EXPORT="$tools_dir/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
export COMPARATOR_NANODA="$tools_dir/nanoda/target/release/nanoda_bin"
npx tsx scripts/verify-submission.ts submissions/<id> --mode=full`;

export default function MethodologyPage() {
  return (
    <main id="main-content">
      <section className="inner-hero methodology-hero shell-wrap">
        <div className="shell inner-hero-grid">
          <div>
            <span className="eyebrow">Verification methodology</span>
            <h1>Untrusted proof.<br />Trusted statement.<br />Two kernels.</h1>
            <p>
              Automation works because acceptance is a deterministic formal check,
              not a judgment about whether an argument looks convincing.
            </p>
          </div>
          <div className="trust-seal" aria-label="Verification guarantees">
            <ShieldCheck size={38} />
            <strong>Kernel verified</strong>
            <span>Exact statement · permitted axioms · isolated replay</span>
          </div>
        </div>
      </section>

      <section className="dark-section methodology-pipeline">
        <div className="shell"><VerificationPipeline /></div>
      </section>

      <section className="shell section-space">
        <div className="section-heading split-heading">
          <div><span className="eyebrow">Separation of powers</span><h2>The proof cannot rewrite the exam</h2></div>
          <p>Verification is split across jobs so pull-request code never receives credentials or write permission.</p>
        </div>
        <div className="trust-grid">
          <article><GitPullRequestArrow size={23} /><h3>Candidate job</h3><p>Checks one added submission and builds it in an isolated, credential-free sandbox. Promotion independently re-verifies the exact commit against the latest record.</p><span className="permission-chip">read-only</span></article>
          <article><FileSearch size={23} /><h3>Comparator</h3><p>Reconstructs trusted declarations and rejects any proof whose statements differ, even if the names match.</p><span className="permission-chip">no secrets</span></article>
          <article><KeyRound size={23} /><h3>Promotion job</h3><p>Runs only after verified CI, rechecks against the latest record, then merges and updates the ledger.</p><span className="permission-chip">write after pass</span></article>
        </div>
      </section>

      <section className="shell methodology-detail">
        <article className="prose-section">
          <span className="eyebrow">Why two kernels?</span>
          <h2>Independent replay narrows the trusted computing base.</h2>
          <p>
            Lean elaborates convenient source code into a compact proof object. The
            Lean kernel checks that object first. Comparator exports it, and nanoda—a
            separate small implementation—checks it again. A frontend bug is not
            enough to advance the record.
          </p>
          <div className="kernel-diagram" aria-label="Proof verification flow">
            <span>Lean source</span><ArrowRight size={16} /><span>Lean kernel</span><ArrowRight size={16} /><span>export</span><ArrowRight size={16} /><span>nanoda</span>
          </div>
        </article>
        <article className="axiom-card">
          <span className="eyebrow">Permitted axioms</span>
          <h3>A short, explicit allowlist</h3>
          <ul>
            {contract.permittedAxioms.map((axiom) => <li key={axiom}><CheckCircle2 size={16} /><code>{axiom}</code></li>)}
          </ul>
          <p>Any additional transitive axiom rejects the submission.</p>
        </article>
      </section>

      <section className="isolation-section">
        <div className="shell isolation-grid">
          <div>
            <span className="eyebrow">Hostile-code model</span>
            <h2>Elaboration is code execution, so CI treats every proof as hostile.</h2>
            <p>Formal correctness is not the same thing as operational safety. Resource limits and filesystem isolation protect the runner while kernels protect the theorem.</p>
          </div>
          <div className="isolation-list">
            <div><Network size={20} /><span><strong>Network restricted</strong><small>Dependencies are pinned and fetched before untrusted code runs; the sandboxed job holds no credentials worth exfiltrating.</small></span></div>
            <div><KeyRound size={20} /><span><strong>Credentials absent</strong><small>The verifier job cannot merge, push, or read repository secrets.</small></span></div>
            <div><Box size={20} /><span><strong>Resources bounded</strong><small>CPU time, memory, processes, and writable paths are restricted.</small></span></div>
          </div>
        </div>
      </section>

      <section className="shell section-space local-check">
        <div>
          <span className="eyebrow">Reproduce it</span>
          <h2>The authoritative command is public.</h2>
          <p>The tool installer checks out every verifier component at the commit recorded in the challenge contract.</p>
          <Link className="text-link" href="/submit">Prepare your submission <ArrowRight size={16} /></Link>
        </div>
        <CodeBlock label="Linux verifier runner">{command}</CodeBlock>
      </section>
    </main>
  );
}
