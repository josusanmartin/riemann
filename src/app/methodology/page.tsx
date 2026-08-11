import type { Metadata } from "next";
import Link from "next/link";
import {
  ArrowRight,
  Box,
  CheckCircle2,
  FileSearch,
  UploadCloud,
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
    "How untrusted Lean code is isolated, how statements are compared, how two kernels replay the proof, and how records are promoted.",
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
            <h1>How submissions are verified.</h1>
            <p>
              Acceptance is a deterministic formal check, so the process runs
              without any human judgment of the argument itself.
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
          <div><span className="eyebrow">Separation of duties</span><h2>Verification and publication use separate trust domains</h2></div>
          <p>Untrusted Lean and the credentialed publisher are separated so proof code can never read or use a write credential.</p>
        </div>
        <div className="trust-grid">
          <article><UploadCloud size={23} /><h3>Candidate sandbox</h3><p>Checks one server-generated manifest and one Lean file in a private, no-egress E2B environment with no application credentials.</p><span className="permission-chip">no secrets</span></article>
          <article><FileSearch size={23} /><h3>Comparator</h3><p>Reconstructs trusted declarations and rejects any proof whose statements differ, even if the names match.</p><span className="permission-chip">no secrets</span></article>
          <article><KeyRound size={23} /><h3>Publisher</h3><p>Rehashes the sandbox source and attestation, then atomically archives evidence and updates the ledger without a pull request.</p><span className="permission-chip">write after pass</span></article>
        </div>
      </section>

      <section className="shell methodology-detail">
        <article className="prose-section">
          <span className="eyebrow">Two independent kernels</span>
          <h2>Independent replay narrows the trusted computing base.</h2>
          <p>
            Lean elaborates source code into a compact proof object, which the Lean
            kernel checks first. Comparator then exports that object, and nanoda, a
            separate small implementation, checks it again. A bug in one checker is
            not enough to advance the record.
          </p>
          <div className="kernel-diagram" aria-label="Proof verification flow">
            <span>Lean source</span><ArrowRight size={16} /><span>Lean kernel</span><ArrowRight size={16} /><span>export</span><ArrowRight size={16} /><span>nanoda</span>
          </div>
        </article>
        <article className="axiom-card">
          <span className="eyebrow">Permitted axioms</span>
          <h3>The permitted axioms</h3>
          <ul>
            {contract.permittedAxioms.map((axiom) => <li key={axiom}><CheckCircle2 size={16} /><code>{axiom}</code></li>)}
          </ul>
          <p>Any additional transitive axiom rejects the submission.</p>
        </article>
      </section>

      <section className="isolation-section">
        <div className="shell isolation-grid">
          <div>
            <span className="eyebrow">Untrusted-code model</span>
            <h2>Elaborating a Lean proof runs code, so the verifier treats every submission as untrusted.</h2>
            <p>Formal correctness does not imply the code is safe to run, so resource limits and filesystem isolation protect the runner while the kernels protect the theorem.</p>
          </div>
          <div className="isolation-list">
            <div><Network size={20} /><span><strong>No outbound network</strong><small>Dependencies are pinned into the template before untrusted code runs, and a live probe must confirm that egress is disabled.</small></span></div>
            <div><KeyRound size={20} /><span><strong>Credentials absent</strong><small>The verifier cannot publish, push, or read application secrets.</small></span></div>
            <div><Box size={20} /><span><strong>Resources bounded</strong><small>CPU time, memory, processes, and writable paths are restricted.</small></span></div>
          </div>
        </div>
      </section>

      <section className="shell section-space local-check">
        <div>
          <span className="eyebrow">Reproduce the check</span>
          <h2>Run the verifier yourself.</h2>
          <p>The tool installer checks out every verifier component at the commit recorded in the challenge contract.</p>
          <Link className="text-link" href="/submit">Prepare your submission <ArrowRight size={16} /></Link>
        </div>
        <CodeBlock label="Linux verifier runner">{command}</CodeBlock>
      </section>
    </main>
  );
}
