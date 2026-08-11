import type { Metadata } from "next";
import { ArrowRight, Check, Github, Terminal, UploadCloud } from "lucide-react";
import { getSession, isGitHubAuthConfigured } from "@/auth";
import { CodeBlock } from "@/components/code-block";
import { signInWithGitHub } from "@/lib/auth-actions";
import { newSubmissionUrl, repositoryUrl } from "@/lib/site";

export const metadata: Metadata = {
  title: "Submit a proof",
  description: "Fork the repository, add an exact rational and Lean proof, then open a formally verified record pull request.",
};

const manifest = `{
  "schemaVersion": 1,
  "id": "your-candidate",
  "track": "critical-line",
  "author": { "github": "your-handle", "displayName": "Your name" },
  "score": { "numerator": "672500704", "denominator": "1000000000" },
  "proof": {
    "solution": "proof/Solution.lean",
    "theorem": "candidate_critical_line_bound",
    "cumulativeTheorem": "candidate_critical_line_bound_cumulative",
    "improvementTheorem": "candidate_strict_improvement"
  },
  "summary": "Describe the formal improvement and its mathematical idea.",
  "method": "Name the method",
  "license": "Apache-2.0"
}`;

export default async function SubmitPage() {
  const session = await getSession();
  const signedIn = Boolean(session?.user);

  return (
    <main id="main-content">
      <section className="inner-hero submit-hero shell-wrap">
        <div className="shell inner-hero-grid">
          <div>
            <span className="eyebrow">Submit a formal improvement</span>
            <h1>Your pull request is the entry form.</h1>
            <p>Fork the public repository, add one candidate directory, and let the same reproducible verifier judge every entry.</p>
            <div className="hero-actions">
              {signedIn ? (
                <a className="button button-lime" href={newSubmissionUrl} target="_blank" rel="noreferrer">
                  Open GitHub compare <ArrowRight size={17} />
                </a>
              ) : isGitHubAuthConfigured ? (
                <form action={signInWithGitHub}>
                  <button className="button button-lime" type="submit"><Github size={17} /> Sign in with GitHub</button>
                </form>
              ) : (
                <a className="button button-lime" href={repositoryUrl} target="_blank" rel="noreferrer"><Github size={17} /> Open repository</a>
              )}
              <a className="button button-ghost-light" href={`${repositoryUrl}/tree/main/submissions/example`} target="_blank" rel="noreferrer">View example</a>
            </div>
            {signedIn && (
              <p className="cta-note">
                The compare button opens GitHub’s branch chooser — fork the repository and push your candidate branch first, then select it there.
              </p>
            )}
          </div>
          <aside className="submit-status-card">
            <span className="eyebrow eyebrow-light">Account</span>
            {signedIn ? (
              <><strong>Signed in as @{session?.user.githubLogin ?? session?.user.name}</strong><p>Your GitHub identity will be linked from a successful record.</p></>
            ) : isGitHubAuthConfigured ? (
              <><strong>Sign in before submitting</strong><p>Authentication requests read-only profile and email access. Proofs still arrive through GitHub.</p></>
            ) : (
              <><strong>Repository submissions are open</strong><p>Site sign-in is awaiting the production OAuth keys; the public PR workflow already works.</p></>
            )}
          </aside>
        </div>
      </section>

      <section className="shell section-space submit-steps">
        <div className="section-heading split-heading">
          <div><span className="eyebrow">Three steps</span><h2>From fork to verified record</h2></div>
          <p>Do not run unfamiliar submissions outside the isolated verifier.</p>
        </div>
        <ol className="numbered-steps">
          <li><span>01</span><div><h3>Copy the example</h3><p>Create <code>submissions/&lt;id&gt;</code> with a manifest and Lean files under <code>proof/</code>.</p></div></li>
          <li><span>02</span><div><h3>Prove all three targets</h3><p>Strict improvement, the dyadic critical-line bound, and its cumulative form must share one exact κ.</p></div></li>
          <li><span>03</span><div><h3>Open one scoped PR</h3><p>CI rejects changes outside the new directory, then verifies and promotes a passing record automatically.</p></div></li>
        </ol>
      </section>

      <section className="shell submission-template">
        <div className="template-copy">
          <span className="eyebrow">Submission manifest</span>
          <h2>The score is data, not prose.</h2>
          <p>Use integer strings for the exact rational. The dashboard derives its decimal representation; it never trusts a rounded score supplied by the author.</p>
          <ul className="check-list">
            <li><Check size={16} /> One new submission directory</li>
            <li><Check size={16} /> Lean source only, no binaries</li>
            <li><Check size={16} /> Apache-2.0 proof license</li>
            <li><Check size={16} /> No changes to trusted paths</li>
          </ul>
        </div>
        <CodeBlock label="submissions/your-candidate/submission.json">{manifest}</CodeBlock>
      </section>

      <section className="shell verify-locally">
        <div className="verify-icon"><Terminal size={25} /></div>
        <div><span className="eyebrow">Before opening the PR</span><h2>Run the quick trusted-code check.</h2><p>Full verification happens in isolated CI. Quick mode builds locally and should only be used on proof code you trust.</p></div>
        <code>npx tsx scripts/verify-submission.ts submissions/your-candidate --mode=quick</code>
      </section>

      <section className="shell submit-final-card">
        <UploadCloud size={31} />
        <div>
          <h2>Ready to move the frontier?</h2>
          <p>A passing exact improvement is accepted by the machine, not by popularity.</p>
          <p className="cta-note">Opens GitHub’s branch-compare chooser — push your fork’s candidate branch first, then select it there.</p>
        </div>
        <a className="button button-dark" href={newSubmissionUrl} target="_blank" rel="noreferrer">Open GitHub compare <ArrowRight size={17} /></a>
      </section>
    </main>
  );
}
