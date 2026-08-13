"use client";

import { useCallback, useEffect, useRef, useState } from "react";
import {
  CheckCircle2,
  Download,
  ExternalLink,
  FileCode2,
  LoaderCircle,
  RotateCcw,
  ShieldCheck,
  Upload,
} from "lucide-react";

type FlowTestPhase =
  | "idle"
  | "starting"
  | "running"
  | "verified"
  | "rejected"
  | "error";

type FlowTestPayload = {
  status?: "running" | "verified" | "rejected";
  jobToken?: string;
  proofDigest?: string;
  message?: string;
  log?: string;
  feedback?: {
    title: string;
    action: string;
    stage: string;
    code: string;
  };
};

const STORAGE_KEY = "riemann.fail:operator-flow-test:v1";
const MAX_FILE_BYTES = 2_000_000;

export function FlowTestPanel({
  officialSource,
  downloadPath,
  gistUrl,
  verifierConfigured,
}: {
  officialSource: string;
  downloadPath: string;
  gistUrl: string;
  verifierConfigured: boolean;
}) {
  const [source, setSource] = useState(officialSource);
  const [phase, setPhase] = useState<FlowTestPhase>("idle");
  const [message, setMessage] = useState(
    "Ready to replay Anthropic's complete two-thirds proof against the isolated test baseline.",
  );
  const [digest, setDigest] = useState("");
  const [log, setLog] = useState("");
  const [feedback, setFeedback] = useState<FlowTestPayload["feedback"]>();
  const pollGeneration = useRef(0);
  const busy = phase === "starting" || phase === "running";

  const poll = useCallback(async (jobToken: string) => {
    const generation = ++pollGeneration.current;
    let transientFailures = 0;
    for (;;) {
      await new Promise((resolve) => window.setTimeout(resolve, 10_000));
      if (pollGeneration.current !== generation) return;
      try {
        const response = await fetch(
          `/api/submissions/flow-test/status?job=${encodeURIComponent(jobToken)}`,
          { cache: "no-store" },
        );
        const payload = (await response.json()) as FlowTestPayload;
        if (!response.ok) {
          if (response.status >= 400 && response.status < 500) {
            window.localStorage.removeItem(STORAGE_KEY);
            setPhase("error");
            setMessage(payload.message ?? "The flow-test job is no longer available.");
            setFeedback(payload.feedback);
            return;
          }
          throw new Error(payload.message ?? "Unable to read the flow-test status.");
        }
        transientFailures = 0;
        setDigest(payload.proofDigest ?? "");
        if (payload.status === "running") {
          setPhase("running");
          setMessage(
            payload.message ?? "Comparator, Lean, and nanoda are replaying the proof.",
          );
          continue;
        }
        window.localStorage.removeItem(STORAGE_KEY);
        setLog(payload.log ?? "");
        setFeedback(payload.feedback);
        if (payload.status === "verified") {
          setPhase("verified");
          setMessage(payload.message ?? "The complete flow-test proof passed.");
        } else {
          setPhase("rejected");
          setMessage(payload.message ?? "The flow-test proof was rejected.");
        }
        return;
      } catch {
        transientFailures += 1;
        setPhase("running");
        setMessage(
          transientFailures < 5
            ? "Flow-test status is temporarily unavailable; retrying automatically."
            : "The signed job is saved in this browser; still reconnecting automatically.",
        );
      }
    }
  }, []);

  useEffect(() => {
    let stored: { jobToken?: string; proofDigest?: string } | null = null;
    try {
      stored = JSON.parse(window.localStorage.getItem(STORAGE_KEY) ?? "null") as {
        jobToken?: string;
        proofDigest?: string;
      } | null;
    } catch {
      window.localStorage.removeItem(STORAGE_KEY);
    }
    const restoreTimer = stored?.jobToken
      ? window.setTimeout(() => {
          setPhase("running");
          setDigest(stored?.proofDigest ?? "");
          setMessage("Recovered the active verifier flow test from this browser.");
          void poll(stored?.jobToken ?? "");
        }, 0)
      : undefined;
    return () => {
      if (restoreTimer !== undefined) window.clearTimeout(restoreTimer);
      pollGeneration.current += 1;
    };
  }, [poll]);

  function resetResult(nextSource = source): void {
    pollGeneration.current += 1;
    setSource(nextSource);
    setPhase("idle");
    setMessage("Ready to run the noncompetitive production-verifier replay.");
    setDigest("");
    setLog("");
    setFeedback(undefined);
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
    resetResult(await file.text());
    setMessage(`${file.name} loaded for the noncompetitive flow test.`);
  }

  async function runFlowTest() {
    if (!verifierConfigured) {
      setPhase("error");
      setMessage("The pinned E2B verifier is not configured for this deployment.");
      return;
    }
    if (new Blob([source]).size > MAX_FILE_BYTES) {
      setPhase("error");
      setMessage("Solution.lean exceeds the 2 MB source limit.");
      return;
    }
    setPhase("starting");
    setMessage("Creating a private no-egress E2B sandbox for the flow test.");
    setDigest("");
    setLog("");
    setFeedback(undefined);
    try {
      const response = await fetch("/api/submissions/flow-test", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ solution: source }),
      });
      const payload = (await response.json()) as FlowTestPayload;
      if (!response.ok || !payload.jobToken) {
        throw new Error(payload.message ?? "The verifier flow test could not start.");
      }
      setPhase("running");
      setDigest(payload.proofDigest ?? "");
      setMessage(payload.message ?? "The full proof replay is running.");
      window.localStorage.setItem(
        STORAGE_KEY,
        JSON.stringify({
          jobToken: payload.jobToken,
          proofDigest: payload.proofDigest ?? "",
        }),
      );
      void poll(payload.jobToken);
    } catch (error) {
      setPhase("error");
      setMessage(
        error instanceof Error ? error.message : "The verifier flow test could not start.",
      );
    }
  }

  return (
    <section
      className="shell flow-test-panel"
      id="verifier-flow-test"
      aria-labelledby="flow-test-title"
    >
      <div className="flow-test-copy">
        <span className="eyebrow">Operator flow test · noncompetitive</span>
        <h2 id="flow-test-title">A complete proof that can turn the verifier green.</h2>
        <p>
          This controlled lane fixes the previous record at <code>1/3</code> and
          the candidate at <code>2/3</code>, then replays Anthropic&apos;s checked
          dyadic and cumulative theorems. It uses the production E2B image,
          Comparator, Lean, and nanoda, but never promotes a record and does not
          consume the three-per-day competitive allowance. A complete two-kernel
          replay can take up to about 55 minutes; the runner reports its live
          stage while it works.
        </p>
        <div className="flow-test-links">
          <a className="button button-dark" href={downloadPath} download="Solution.lean">
            <Download size={16} /> Download full proof
          </a>
          <a className="text-link" href={gistUrl} target="_blank" rel="noreferrer">
            Open public Gist <ExternalLink size={14} />
          </a>
        </div>
        <ul className="template-check-list">
          <li><ShieldCheck size={15} /> Same immutable verifier and permitted-axiom audit</li>
          <li><ShieldCheck size={15} /> Serialized behind any active competitive proof</li>
          <li><ShieldCheck size={15} /> Test result is never added to the leaderboard</li>
        </ul>
      </div>

      <div className="flow-test-runner">
        <div className="lean-source-heading">
          <div><FileCode2 size={19} /><span>Solution.lean · full test proof</span></div>
          <div className="lean-source-actions">
            <button
              className="starter-picker"
              type="button"
              onClick={() => resetResult(officialSource)}
              disabled={busy}
            >
              <RotateCcw size={14} /> Restore official proof
            </button>
            <label className="file-picker">
              <Upload size={14} /> Upload .lean
              <input type="file" accept=".lean,text/plain" onChange={loadFile} disabled={busy} />
            </label>
          </div>
        </div>
        <textarea
          aria-label="Flow-test Lean source"
          className="flow-test-editor"
          value={source}
          onChange={(event) => resetResult(event.target.value)}
          spellCheck={false}
          disabled={busy}
        />
        <div className={`verification-job-card flow-test-result ${phase}`} aria-live="polite">
          <div className="job-icon">
            {busy ? (
              <LoaderCircle className="spin" size={22} />
            ) : phase === "verified" ? (
              <CheckCircle2 size={22} />
            ) : (
              <ShieldCheck size={22} />
            )}
          </div>
          <div>
            <strong>
              {phase === "verified"
                ? "Both kernels accepted the full proof"
                : phase === "rejected"
                  ? feedback?.title ?? "Flow-test proof rejected"
                  : busy
                    ? "Production verifier replay running"
                    : "Ready for a safe green-path test"}
            </strong>
            <p>{message}</p>
            {digest && <code>sha256:{digest}</code>}
          </div>
          <button
            className="button button-lime"
            type="button"
            onClick={runFlowTest}
            disabled={busy || !source || !verifierConfigured}
          >
            {busy ? "Checking…" : "Run full flow test"}
          </button>
        </div>
        {feedback && (
          <div className="flow-test-feedback">
            <strong>{feedback.stage} · {feedback.code}</strong>
            <p>{feedback.action}</p>
          </div>
        )}
        {log && (
          <details className="verification-log">
            <summary>Technical verifier log</summary>
            <pre>{log}</pre>
          </details>
        )}
      </div>
    </section>
  );
}
