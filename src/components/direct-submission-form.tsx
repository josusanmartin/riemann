"use client";

import { useCallback, useEffect, useRef, useState } from "react";
import {
  CheckCircle2,
  FileCode2,
  FilePlus2,
  LoaderCircle,
  ShieldAlert,
  Upload,
} from "lucide-react";

type JobPhase =
  | "idle"
  | "starting"
  | "queued"
  | "running"
  | "verified"
  | "superseded"
  | "rejected"
  | "error";

type VerifierFeedbackPayload = {
  code: string;
  stage: string;
  title: string;
  detail: string;
  action: string;
  retryable: boolean;
  location?: {
    file: "Solution.lean";
    line: number;
    column: number;
  };
};

type StatusPayload = {
  status?: "queued" | "running" | "verified" | "rejected";
  submissionId?: string;
  proofDigest?: string;
  message?: string;
  log?: string;
  jobToken?: string;
  queuePosition?: number;
  dailyUsed?: number;
  dailyLimit?: number;
  feedback?: VerifierFeedbackPayload;
  promotion?: {
    status?: string;
    message?: string;
    evidenceUrl?: string;
  };
};

type RecoveryPayload = Omit<StatusPayload, "status"> & {
  status?: StatusPayload["status"] | "none";
};

const MAX_FILE_BYTES = 2_000_000;
const ACTIVE_JOB_STORAGE_PREFIX = "riemann.fail:active-verification:v1";

const feedbackStageLabels: Record<string, string> = {
  submission: "Submission intake",
  "lean-compilation": "Lean compilation",
  "theorem-contract": "Theorem contract",
  "axiom-audit": "Axiom audit",
  "nanoda-kernel": "Nanoda kernel",
  "lean-kernel": "Lean kernel",
  runtime: "Runtime limit",
  infrastructure: "Verifier infrastructure",
  unknown: "Unclassified verifier stage",
};

type StoredActiveJob = {
  jobToken: string;
  proofDigest: string;
};

function readStoredActiveJob(storageKey: string): StoredActiveJob | null {
  try {
    const value = JSON.parse(window.localStorage.getItem(storageKey) ?? "null") as unknown;
    if (
      typeof value === "object" &&
      value !== null &&
      "jobToken" in value &&
      typeof value.jobToken === "string" &&
      value.jobToken.length > 0 &&
      "proofDigest" in value &&
      typeof value.proofDigest === "string" &&
      /^[0-9a-f]{64}$/.test(value.proofDigest)
    ) {
      return value as StoredActiveJob;
    }
  } catch {
    // Treat corrupt or unavailable browser storage as an absent job handle.
  }
  return null;
}

function storeActiveJob(storageKey: string, job: StoredActiveJob): void {
  try {
    window.localStorage.setItem(storageKey, JSON.stringify(job));
  } catch {
    // Verification still works in browsers that block local storage; only
    // cross-refresh recovery is unavailable.
  }
}

function clearActiveJob(storageKey: string): void {
  try {
    window.localStorage.removeItem(storageKey);
  } catch {
    // Nothing else is required when browser storage is unavailable.
  }
}

export function DirectSubmissionForm({
  github,
  defaultDisplayName,
  verifierConfigured,
  starterSource,
}: {
  github: string;
  defaultDisplayName: string;
  verifierConfigured: boolean;
  starterSource: string;
}) {
  const [solution, setSolution] = useState("");
  const [phase, setPhase] = useState<JobPhase>("idle");
  const [message, setMessage] = useState("");
  const [log, setLog] = useState("");
  const [feedback, setFeedback] = useState<VerifierFeedbackPayload | null>(null);
  const [digest, setDigest] = useState("");
  const [evidenceUrl, setEvidenceUrl] = useState("");
  const pollGeneration = useRef(0);
  const storageKey = `${ACTIVE_JOB_STORAGE_PREFIX}:${github.toLowerCase()}`;
  const busy = phase === "starting" || phase === "queued" || phase === "running";

  function replaceEditorSource(nextSource: string, nextMessage: string): void {
    setSolution(nextSource);
    setPhase("idle");
    setMessage(nextMessage);
    setLog("");
    setFeedback(null);
    setDigest("");
    setEvidenceUrl("");
  }

  const poll = useCallback(async (jobToken: string) => {
    const generation = ++pollGeneration.current;
    let transientFailures = 0;
    let delayMs = 5_000;
    for (;;) {
      await new Promise((resolve) => window.setTimeout(resolve, delayMs));
      if (pollGeneration.current !== generation) return;
      try {
        const response = await fetch(
          `/api/submissions/status?job=${encodeURIComponent(jobToken)}`,
          { cache: "no-store" },
        );
        const payload = (await response.json()) as StatusPayload;
        if (!response.ok) {
          if (response.status >= 400 && response.status < 500) {
            clearActiveJob(storageKey);
            setFeedback(payload.feedback ?? null);
            setPhase(payload.feedback ? "rejected" : "error");
            setMessage(payload.message ?? "This verification job is no longer available.");
            return;
          }
          throw new Error(payload.message ?? "Unable to read verifier status.");
        }
        transientFailures = 0;

        if (payload.status === "queued") {
          delayMs = 15_000;
          setPhase("queued");
          setMessage(
            `Queued for linear verification · ${payload.queuePosition ?? 1} ${
              payload.queuePosition === 1 ? "proof" : "proofs"
            } ahead.`,
          );
          continue;
        }
        if (payload.status === "running") {
          delayMs = 5_000;
          setPhase("running");
          setMessage(
            "Lean and both kernels are checking the frozen theorem contract.",
          );
          continue;
        }

        setDigest(payload.proofDigest ?? "");
        setLog(payload.log ?? "");
        setFeedback(payload.feedback ?? null);
        clearActiveJob(storageKey);
        if (payload.status === "verified") {
          if (payload.promotion?.status === "superseded") {
            setPhase("superseded");
            setMessage(
              payload.promotion.message ??
                "The proof passed, but another record landed first. Verify again against the new record.",
            );
          } else {
            setPhase("verified");
            setEvidenceUrl(payload.promotion?.evidenceUrl ?? "");
            setMessage(
              payload.promotion?.status === "promoted" ||
                payload.promotion?.status === "already-promoted"
                ? "Lean and nanoda accepted the source, and the new record is now published."
                : payload.promotion?.message ??
                    "Lean and nanoda accepted the exact uploaded source.",
            );
          }
        } else {
          setPhase("rejected");
          setMessage(
            payload.message ?? "The formal verifier rejected this candidate.",
          );
        }
        return;
      } catch {
        transientFailures += 1;
        delayMs = Math.min(60_000, 5_000 * 2 ** Math.min(transientFailures, 4));
        setPhase("running");
        setMessage(
          transientFailures <= 6
            ? "Verifier status is temporarily unavailable; retrying automatically."
            : "The verification is still saved in this browser; reconnecting automatically.",
        );
      }
    }
  }, [storageKey]);

  useEffect(() => {
    let cancelled = false;
    const restore = async () => {
      let storedJob = readStoredActiveJob(storageKey);
      let recoveredStatus: "queued" | "running" = "running";
      let queuePosition: number | undefined;
      if (!storedJob) {
        try {
          const response = await fetch("/api/submissions/active", {
            cache: "no-store",
          });
          const payload = (await response.json()) as RecoveryPayload;
          if (
            !response.ok ||
            payload.status === "none" ||
            !payload.jobToken ||
            !payload.proofDigest ||
            !/^[0-9a-f]{64}$/.test(payload.proofDigest)
          ) {
            return;
          }
          storedJob = {
            jobToken: payload.jobToken,
            proofDigest: payload.proofDigest,
          };
          recoveredStatus = payload.status === "queued" ? "queued" : "running";
          queuePosition = payload.queuePosition;
          storeActiveJob(storageKey, storedJob);
        } catch {
          return;
        }
      }
      if (cancelled) return;
      setDigest(storedJob.proofDigest);
      setPhase(recoveredStatus);
      setMessage(
        recoveredStatus === "queued"
          ? `Recovered queued verification · position ${queuePosition ?? 1}.`
          : "Recovered the active verification job. Reconnecting now.",
      );
      void poll(storedJob.jobToken);
    };
    const restoreTimer = window.setTimeout(() => void restore(), 0);
    return () => {
      cancelled = true;
      window.clearTimeout(restoreTimer);
      pollGeneration.current += 1;
    };
  }, [poll, storageKey]);

  async function submit(event: React.FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setLog("");
    setFeedback(null);
    setDigest("");
    setEvidenceUrl("");
    if (!verifierConfigured) {
      setPhase("error");
      setMessage("The pinned E2B verifier template is still being configured.");
      return;
    }
    const starterPlaceholders = solution.match(/^\s{2}sorry\s*$/gm)?.length ?? 0;
    if (starterPlaceholders > 0) {
      setPhase("error");
      setMessage(
        `Replace the ${starterPlaceholders} starter sorry placeholder${starterPlaceholders === 1 ? "" : "s"} before verifying. Nothing was submitted, so no daily slot was used.`,
      );
      return;
    }
    if (new Blob([solution]).size > MAX_FILE_BYTES) {
      setPhase("error");
      setMessage("Solution.lean exceeds the 2 MB source limit.");
      return;
    }

    setPhase("starting");
    setMessage("Creating a private no-egress E2B sandbox.");
    const form = new FormData(event.currentTarget);
    const model = (form.get("model")?.toString() ?? "").trim();
    const harness = (form.get("harness")?.toString() ?? "").trim();
    try {
      const response = await fetch("/api/submissions", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          id: form.get("id"),
          displayName: form.get("displayName"),
          score: {
            numerator: form.get("numerator"),
            denominator: form.get("denominator"),
          },
          summary: form.get("summary"),
          method: form.get("method"),
          model: model || null,
          harness: harness || null,
          solution,
          acceptLicense: form.get("acceptLicense") === "on",
        }),
      });
      const payload = (await response.json()) as StatusPayload;
      if (!response.ok || !payload.jobToken) {
        throw new Error(payload.message ?? "The verifier could not start.");
      }
      const queued = payload.status === "queued";
      setPhase(queued ? "queued" : "running");
      setDigest(payload.proofDigest ?? "");
      setMessage(
        queued
          ? `Upload sealed · queue position ${payload.queuePosition ?? 1}. ${
              payload.dailyUsed ?? 1
            }/${payload.dailyLimit ?? 3} submissions used today.`
          : `Upload sealed. Formal verification is running · ${
              payload.dailyUsed ?? 1
            }/${payload.dailyLimit ?? 3} submissions used today.`,
      );
      storeActiveJob(storageKey, {
        jobToken: payload.jobToken,
        proofDigest: payload.proofDigest ?? "",
      });
      void poll(payload.jobToken);
    } catch (error) {
      setPhase("error");
      setMessage(error instanceof Error ? error.message : "The verifier could not start.");
    }
  }

  async function loadFile(event: React.ChangeEvent<HTMLInputElement>) {
    const file = event.target.files?.[0];
    if (!file) return;
    if (!file.name.endsWith(".lean") || file.size > MAX_FILE_BYTES) {
      setPhase("error");
      setMessage("Choose one .lean source file no larger than 2 MB.");
      event.target.value = "";
      return;
    }
    replaceEditorSource(
      await file.text(),
      `${file.name} loaded into the source editor.`,
    );
  }

  function loadStarterTemplate(): void {
    replaceEditorSource(
      starterSource,
      "Starter loaded. Replace all three sorry placeholders before submitting.",
    );
  }

  return (
    <form className="direct-submission-form" onSubmit={submit}>
      <div className="submission-fields">
        <label>
          <span>Record name</span>
          <input name="id" required maxLength={80} pattern="[a-z0-9][a-z0-9-]*" placeholder="your-bound-2026" disabled={busy} />
          <small>A short identifier for this record — lowercase letters, digits, and hyphens. It becomes the record’s URL and its entry in the public ledger, so pick something recognizable.</small>
        </label>
        <label>
          <span>Public author</span>
          <input name="displayName" required maxLength={100} defaultValue={defaultDisplayName} disabled={busy} />
          <small>Bound server-side to @{github}.</small>
        </label>
        <label>
          <span>Exact numerator p</span>
          <input name="numerator" required maxLength={200} inputMode="numeric" pattern="[1-9][0-9]*" placeholder="672500704" disabled={busy} />
        </label>
        <label>
          <span>Exact denominator q</span>
          <input name="denominator" required maxLength={200} inputMode="numeric" pattern="[1-9][0-9]*" placeholder="1000000000" disabled={busy} />
        </label>
        <label className="field-wide">
          <span>Method</span>
          <input name="method" required minLength={3} maxLength={200} placeholder="Name the mathematical method" disabled={busy} />
        </label>
        <label>
          <span>AI model <span className="optional">optional</span></span>
          <input name="model" maxLength={80} placeholder="e.g. Claude Opus 4.8, GPT-5" disabled={busy} />
          <small>The model that produced the proof. Credited in the public record.</small>
        </label>
        <label>
          <span>Coding agent or harness <span className="optional">optional</span></span>
          <input name="harness" maxLength={80} placeholder="e.g. Claude Code, autoresearch" disabled={busy} />
          <small>Any agent or harness you used to generate or drive the proof.</small>
        </label>
        <label className="field-wide">
          <span>Summary</span>
          <textarea name="summary" required minLength={20} maxLength={1000} rows={4} placeholder="Describe the formal improvement and its mathematical idea." disabled={busy} />
          <small>Up to 1,000 characters. Model and harness attribution are stored separately.</small>
        </label>
      </div>

      <div className="lean-source-field">
        <div className="lean-source-heading">
          <div><FileCode2 size={20} /><span>proof/Solution.lean</span></div>
          <div className="lean-source-actions">
            <button
              className="starter-picker"
              type="button"
              onClick={loadStarterTemplate}
              disabled={busy}
            >
              <FilePlus2 size={15} /> Use starter
            </button>
            <label className="file-picker">
              <Upload size={15} /> Upload .lean
              <input type="file" accept=".lean,text/plain" onChange={loadFile} disabled={busy} />
            </label>
          </div>
        </div>
        <textarea
          aria-label="Lean source"
          className="lean-editor"
          required
          value={solution}
          onChange={(event) => {
            const nextSolution = event.target.value;
            if (phase === "idle") {
              setSolution(nextSolution);
            } else {
              replaceEditorSource(nextSolution, "Source changed. Ready to verify again.");
            }
          }}
          placeholder="Paste the three complete Lean theorem declarations here…"
          spellCheck={false}
          disabled={busy}
        />
        <div className="source-meter">
          <span>{new Blob([solution]).size.toLocaleString()} / {MAX_FILE_BYTES.toLocaleString()} bytes</span>
          <span>Plain Lean source only</span>
        </div>
      </div>

      <label className="license-consent">
        <input name="acceptLicense" type="checkbox" required disabled={busy} />
        <span>I publish this proof source under Apache-2.0 for verification and permanent public evidence if accepted.</span>
      </label>

      <div className={`verification-job-card ${phase}`} aria-live="polite">
        <div className="job-icon">
          {busy ? <LoaderCircle className="spin" size={23} /> : phase === "verified" ? <CheckCircle2 size={23} /> : <ShieldAlert size={23} />}
        </div>
        <div>
          <strong>{phase === "idle" ? "Ready for isolated verification" : phase === "verified" ? "Kernel verified and published" : phase === "superseded" ? "Verified against an older record" : phase === "rejected" ? feedback?.title ?? "Proof rejected" : phase === "error" ? "Submission unavailable" : phase === "queued" ? "Waiting in the verification queue" : "Verification running"}</strong>
          <p>{message || "Nothing is accepted until Lean and nanoda independently replay the proof."}</p>
          {digest && <code>sha256:{digest}</code>}
          {evidenceUrl && <a href={evidenceUrl} target="_blank" rel="noreferrer">Open immutable evidence</a>}
        </div>
        <button className="button button-dark" type="submit" disabled={busy || !solution}>
          {phase === "queued" ? "Queued…" : busy ? "Checking…" : "Verify formal proof"}
        </button>
      </div>

      {phase === "rejected" && feedback && (
        <section className="verification-feedback" aria-label="Verifier diagnosis">
          <div className="verification-feedback-meta">
            <span>
              Failed at {feedbackStageLabels[feedback.stage] ?? "Verification"}
              {feedback.location
                ? ` · ${feedback.location.file}:${feedback.location.line}:${feedback.location.column}`
                : ""}
            </span>
            <code>{feedback.code}</code>
          </div>
          <h4>What to do next</h4>
          <p>{feedback.action}</p>
          <small>
            {feedback.retryable
              ? "The checker marked this as retryable infrastructure trouble; it is not a mathematical rejection."
              : "Change or diagnose the source before using another daily submission."}
          </small>
        </section>
      )}

      {log && <details className="verification-log"><summary>Technical verifier log (not published)</summary><pre>{log}</pre></details>}
    </form>
  );
}
