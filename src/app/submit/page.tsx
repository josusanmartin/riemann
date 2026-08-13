import type { Metadata } from "next";
import Link from "next/link";
import {
  Check,
  Clock3,
  Download,
  FileCode2,
  Github,
  ShieldCheck,
  UploadCloud,
} from "lucide-react";
import { getSession, isGitHubAuthConfigured } from "@/auth";
import { CodeBlock } from "@/components/code-block";
import { DirectSubmissionForm } from "@/components/direct-submission-form";
import { FlowTestPanel } from "@/components/flow-test-panel";
import { signInWithGitHub } from "@/lib/auth-actions";
import { getCurrentRecord } from "@/lib/records";
import { isE2BConfigured } from "@/lib/e2b-config";
import { isE2BWebhookConfigured } from "@/lib/e2b-webhooks";
import { isGitHubPromotionConfigured } from "@/lib/github-promotion";
import {
  FLOW_TEST_DOWNLOAD_PATH,
  FLOW_TEST_GIST_URL,
  flowTestSolutionSource,
  isFlowTestOperator,
} from "@/lib/flow-test";
import {
  getDailySubmissionUsage,
  isSubmissionQueueConfigured,
  MAX_DAILY_SUBMISSIONS,
} from "@/lib/submission-queue";
import {
  SUBMISSION_STARTER_PATH,
  submissionStarterSource,
} from "@/lib/submission-starter";

export const metadata: Metadata = {
  title: "Submit a proof",
  description:
    "Upload an exact rational and Lean proof for isolated two-kernel verification.",
};

export default async function SubmitPage() {
  const session = await getSession();
  const github = session?.user.githubLogin;
  const current = getCurrentRecord();
  const queueConfigured = isSubmissionQueueConfigured();
  const flowTestAllowed = github ? isFlowTestOperator(github) : false;
  const verifierConfigured =
    isE2BConfigured() &&
    isE2BWebhookConfigured() &&
    isGitHubPromotionConfigured() &&
    queueConfigured;
  const dailyUsage =
    github && queueConfigured
      ? await getDailySubmissionUsage(github).catch((error) => {
          console.error("Unable to read the submitter's daily usage", error);
          return null;
        })
      : null;
  const uploadsRemaining = dailyUsage
    ? Math.max(0, dailyUsage.limit - dailyUsage.used)
    : MAX_DAILY_SUBMISSIONS;

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
              Lean kernel, and nanoda. Jobs run one at a time in submission order,
              with three admitted uploads per GitHub account per UTC calendar day.
              The budget resets at 00:00 UTC, and a rejected job still counts once
              queued. No pull request is required.
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
              source enters a disposable, no-egress verifier with fixed tools;
              queued sandboxes remain paused until their turn.
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
          <li><span>02</span><div><h3>Verify in E2B</h3><p>A durable FIFO starts exactly one no-egress VM checker at a time, then checks statement equality, permitted axioms, Lean, and independent nanoda replay.</p></div></li>
          <li><span>03</span><div><h3>Publish evidence</h3><p>A passing result is bound to the exact source digest before it can enter the public record.</p></div></li>
        </ol>
      </section>

      <section className="shell submission-template" id="starter-template">
        <div className="template-copy">
          <span className="eyebrow">One-file starter</span>
          <h2>Keep the signatures. Replace every <code>sorry</code>.</h2>
          <p>
            The form supplies your exact rational. Submit only this Lean file;
            helper declarations and extra imports must live in it. The server
            generates the manifest and both κ definitions.
          </p>
          <div className="template-actions">
            <a
              className="button button-dark"
              href={SUBMISSION_STARTER_PATH}
              download="Solution.lean"
            >
              <Download size={17} /> Download Solution.lean
            </a>
            <Link className="text-link" href="/challenge">
              Read the locked contract
            </Link>
          </div>
          <ul className="template-check-list">
            <li><Check size={15} /> Exactly three required theorem declarations</li>
            <li><Check size={15} /> One UTF-8 Lean file, at most 2 MB</li>
            <li><Check size={15} /> No <code>sorry</code>, custom axioms, or RH assumption</li>
          </ul>
        </div>
        <CodeBlock label="Solution.lean · downloadable starter">
          {submissionStarterSource}
        </CodeBlock>
      </section>

      <section className="shell submission-rate-card" aria-label="Submission rate limit">
        <div className="rate-limit-icon"><Clock3 size={25} /></div>
        <div className="rate-limit-copy">
          <span className="eyebrow eyebrow-light">Rate limit · UTC calendar day</span>
          <strong>
            {dailyUsage
              ? `${uploadsRemaining} of ${dailyUsage.limit} uploads remaining today`
              : `${MAX_DAILY_SUBMISSIONS} admitted uploads per GitHub account per day`}
          </strong>
          <p>
            A slot is charged only after an upload enters the durable FIFO. From
            that point every outcome counts—including Lean errors, statement or
            axiom mismatch, kernel rejection, timeout, and sandbox expiration.
            Requests rejected before queue admission do not consume a slot, and
            admitted slots are not automatically refunded.
          </p>
        </div>
        <dl className="rate-limit-facts">
          <div><dt>Used</dt><dd>{dailyUsage ? `${dailyUsage.used}/${dailyUsage.limit}` : "Sign in to view"}</dd></div>
          <div><dt>Reset</dt><dd>{dailyUsage ? `${dailyUsage.retryAt.slice(0, 10)} 00:00 UTC` : "00:00 UTC"}</dd></div>
          <div><dt>Queue</dt><dd>1 verifier at a time</dd></div>
        </dl>
      </section>

      {flowTestAllowed && (
        <FlowTestPanel
          officialSource={flowTestSolutionSource}
          downloadPath={FLOW_TEST_DOWNLOAD_PATH}
          gistUrl={FLOW_TEST_GIST_URL}
          verifierConfigured={isE2BConfigured()}
        />
      )}

      <section className="shell direct-submit-section">
        <div className="direct-submit-heading">
          <div>
            <span className="eyebrow">Competitive direct verifier</span>
            <h2>Submit a real record improvement</h2>
            <p>
              This form consumes a daily slot after queue admission. The complete
              <code> 1/3 → 2/3 </code> test proof belongs in the noncompetitive
              flow-test lane above, not here.
            </p>
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
            starterSource={submissionStarterSource}
            flowTestSource={flowTestSolutionSource}
            flowTestAvailable={flowTestAllowed}
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
          <li><FileCode2 size={15} /> Starter available above</li>
          <li><Check size={15} /> Lean source only</li>
          <li><Check size={15} /> 2 MB maximum</li>
          <li><Check size={15} /> 3 admitted uploads per account per UTC day</li>
          <li><Check size={15} /> FIFO · 1 verifier at a time</li>
          <li><Check size={15} /> Apache-2.0</li>
        </ul>
      </section>
    </main>
  );
}
