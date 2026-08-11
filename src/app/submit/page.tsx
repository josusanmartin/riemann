import type { Metadata } from "next";
import { Check, Github, ShieldCheck, UploadCloud } from "lucide-react";
import { getSession, isGitHubAuthConfigured } from "@/auth";
import { signInWithGitHub } from "@/lib/auth-actions";
import { getCurrentRecord } from "@/lib/records";
import { isE2BConfigured } from "@/lib/e2b-config";
import { isE2BWebhookConfigured } from "@/lib/e2b-webhooks";
import { isGitHubPromotionConfigured } from "@/lib/github-promotion";
import { DirectSubmissionForm } from "@/components/direct-submission-form";

export const metadata: Metadata = {
  title: "Submit a proof",
  description:
    "Upload an exact rational and Lean proof for isolated two-kernel verification.",
};

export default async function SubmitPage() {
  const session = await getSession();
  const github = session?.user.githubLogin;
  const current = getCurrentRecord();
  const verifierConfigured =
    isE2BConfigured() &&
    isE2BWebhookConfigured() &&
    isGitHubPromotionConfigured();

  return (
    <main id="main-content">
      <section className="inner-hero submit-hero shell-wrap">
        <div className="shell inner-hero-grid">
          <div>
            <span className="eyebrow">Submit a formal improvement</span>
            <h1>Upload a Lean proof for verification.</h1>
            <p>
              Enter an exact rational and paste or upload your Lean source. A
              private E2B sandbox rechecks the fixed theorem with Comparator, the
              Lean kernel, and nanoda. No pull request is required.
            </p>
            {!github && isGitHubAuthConfigured && (
              <form action={signInWithGitHub}>
                <button className="button button-lime" type="submit">
                  <Github size={17} /> Sign in to submit
                </button>
              </form>
            )}
          </div>
          <aside className="submit-status-card">
            <span className="eyebrow eyebrow-light">Submission boundary</span>
            <strong>
              {github ? `Authenticated as @${github}` : "GitHub identity required"}
            </strong>
            <p>
              The browser never receives an E2B or repository credential. Your
              source enters a disposable, no-egress verifier with fixed tools.
            </p>
          </aside>
        </div>
      </section>

      <section className="shell section-space submit-steps">
        <div className="section-heading split-heading">
          <div>
            <span className="eyebrow">The process</span>
            <h2>From source to proof object</h2>
          </div>
          <p>The public number changes only after both kernels accept.</p>
        </div>
        <ol className="numbered-steps">
          <li><span>01</span><div><h3>Upload source</h3><p>The server derives your author identity and a strict manifest from the signed GitHub session.</p></div></li>
          <li><span>02</span><div><h3>Verify in E2B</h3><p>A no-egress VM checks statement equality, permitted axioms, Lean, and independent nanoda replay.</p></div></li>
          <li><span>03</span><div><h3>Publish evidence</h3><p>A passing result is bound to the exact source digest before it can enter the public record.</p></div></li>
        </ol>
      </section>

      <section className="shell direct-submit-section">
        <div className="direct-submit-heading">
          <div>
            <span className="eyebrow">Direct verifier</span>
            <h2>An exact score and a Lean entry file</h2>
          </div>
          <div className="current-record-chip">
            <span>Current formal record</span>
            <code>
              {current.exactRational
                ? `${current.exactRational.numerator}/${current.exactRational.denominator}`
                : current.exactExpression}
            </code>
          </div>
        </div>

        {github ? (
          <DirectSubmissionForm
            github={github}
            defaultDisplayName={session?.user.name ?? github}
            verifierConfigured={verifierConfigured}
          />
        ) : (
          <div className="submission-locked-card">
            <ShieldCheck size={28} />
            <div>
              <h3>Sign in before uploading proof code</h3>
              <p>The authenticated GitHub login becomes the immutable public author field.</p>
            </div>
            {isGitHubAuthConfigured ? (
              <form action={signInWithGitHub}>
                <button className="button button-dark" type="submit"><Github size={17} /> Sign in with GitHub</button>
              </form>
            ) : (
              <span className="verification-badge paper">OAuth unavailable</span>
            )}
          </div>
        )}
      </section>

      <section className="shell submit-final-card">
        <UploadCloud size={31} />
        <div>
          <h2>Browser checks are only a preview.</h2>
          <p>Exact acceptance is recomputed inside the isolated, pinned environment; the checks shown here do not determine the result.</p>
        </div>
        <ul className="inline-proof-rules">
          <li><Check size={15} /> Lean source only</li>
          <li><Check size={15} /> 2 MB maximum</li>
          <li><Check size={15} /> Apache-2.0</li>
        </ul>
      </section>
    </main>
  );
}
