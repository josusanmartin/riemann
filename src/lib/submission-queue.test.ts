import { createHash } from "node:crypto";
import { describe, expect, it } from "vitest";
import { computeDirectProofDigest } from "@/lib/direct-submission";
import { openSubmissionArchive, submissionArchivePath } from "@/lib/submission-archive";
import {
  completeQueueState,
  createEmptyQueueState,
  DailySubmissionLimitError,
  enqueueVerificationJob,
  enqueueQueueState,
  getDailySubmissionUsage,
  inspectOwnerQueueState,
  inspectQueueState,
  MAX_DAILY_SUBMISSIONS,
  replaceActiveQueueState,
  SubmissionAlreadyQueuedError,
} from "@/lib/submission-queue";

const ownerSecret = "queue-test-secret";
const archiveKey = Buffer.alloc(32, 9).toString("base64");
const firstDay = new Date("2026-08-11T10:30:00.000Z");

function input(index: number, submissionId = `record-${index}`) {
  return {
    sandboxId: `sandbox-${String(index).padStart(10, "0")}`,
    jobId: `00000000-0000-4000-8000-${String(index).padStart(12, "0")}`,
    proofDigest: index.toString(16).padStart(64, "0"),
    submissionId,
  };
}

function sha(value: string): string {
  return createHash("sha1").update(value).digest("hex");
}

function archivedInput(
  index: number,
  github: string,
  submissionId = `record-${index}`,
) {
  const solution = `import Challenge\n\n-- archive test ${index}\n`;
  const manifest = `${JSON.stringify(
    {
      schemaVersion: 1,
      id: submissionId,
      track: "critical-line",
      author: { github, displayName: "Queue Tester" },
      score: { numerator: "672500704", denominator: "1000000000" },
      proof: {
        solution: "proof/Solution.lean",
        theorem: "candidate_critical_line_bound",
        cumulativeTheorem: "candidate_critical_line_bound_cumulative",
        improvementTheorem: "candidate_strict_improvement",
      },
      summary: "A complete formal queue archive integration test proof.",
      method: "Queue archive integration test",
      model: null,
      harness: null,
      license: "Apache-2.0",
    },
    null,
    2,
  )}\n`;
  return {
    input: {
      ...input(index, submissionId),
      proofDigest: computeDirectProofDigest(manifest, solution),
    },
    archive: { manifest, solution },
  };
}

function fakeQueueGitHub() {
  const main = "a".repeat(40);
  let queueHead: string | null = null;
  let sequence = 0;
  let requestCount = 0;
  const blobs = new Map<string, string>();
  const trees = new Map<string, Map<string, string>>([
    ["b".repeat(40), new Map()],
  ]);
  const commits = new Map<string, { tree: string; parent: string | null }>([
    [main, { tree: "b".repeat(40), parent: null }],
  ]);
  let patchBarrier:
    | {
        remaining: number;
        promise: Promise<void>;
        release: () => void;
      }
    | undefined;

  const fetchImplementation: typeof fetch = async (request, init = {}) => {
    requestCount += 1;
    const url = new URL(
      typeof request === "string" ? request : request.toString(),
    );
    const method = init.method ?? "GET";
    const body = typeof init.body === "string" ? JSON.parse(init.body) : undefined;
    const response = (value: unknown, status = 200) =>
      new Response(JSON.stringify(value), {
        status,
        headers: { "Content-Type": "application/json" },
      });

    if (url.pathname.endsWith("/git/ref/heads/main") && method === "GET") {
      return response({ object: { sha: main } });
    }
    if (
      url.pathname.endsWith("/git/ref/heads/automation-queue") &&
      method === "GET"
    ) {
      return queueHead
        ? response({ object: { sha: queueHead } })
        : response({ message: "Not Found" }, 404);
    }
    if (url.pathname.includes("/git/commits/") && method === "GET") {
      const commit = url.pathname.split("/").at(-1) ?? "";
      return response({ sha: commit, tree: { sha: commits.get(commit)?.tree } });
    }
    if (url.pathname.endsWith("/git/blobs") && method === "POST") {
      const content = String((body as { content: string }).content);
      const blob = sha(`blob-${sequence += 1}-${content}`);
      blobs.set(blob, content);
      return response({ sha: blob }, 201);
    }
    if (url.pathname.endsWith("/git/trees") && method === "POST") {
      const parsed = body as {
        base_tree: string;
        tree: Array<{ path: string; sha: string }>;
      };
      const files = new Map(trees.get(parsed.base_tree) ?? []);
      for (const entry of parsed.tree) files.set(entry.path, entry.sha);
      const tree = sha(
        `tree-${sequence += 1}-${JSON.stringify([...files.entries()].sort())}`,
      );
      trees.set(tree, files);
      return response({ sha: tree }, 201);
    }
    if (url.pathname.endsWith("/git/commits") && method === "POST") {
      const tree = String((body as { tree: string }).tree);
      const commit = sha(`commit-${sequence += 1}-${tree}`);
      const parent = String((body as { parents: string[] }).parents[0]);
      commits.set(commit, { tree, parent });
      return response({ sha: commit }, 201);
    }
    if (url.pathname.endsWith("/git/refs") && method === "POST") {
      queueHead = String((body as { sha: string }).sha);
      return response({ object: { sha: queueHead } }, 201);
    }
    if (
      url.pathname.endsWith("/git/refs/heads/automation-queue") &&
      method === "PATCH"
    ) {
      const barrier = patchBarrier;
      if (barrier) {
        barrier.remaining -= 1;
        if (barrier.remaining === 0) {
          patchBarrier = undefined;
          barrier.release();
        }
        await barrier.promise;
      }
      const candidate = String((body as { sha: string }).sha);
      if (queueHead && commits.get(candidate)?.parent !== queueHead) {
        return response({ message: "Update is not a fast forward" }, 422);
      }
      queueHead = candidate;
      return response({ object: { sha: queueHead } });
    }
    if (url.pathname.includes("/contents/")) {
      const ref = url.searchParams.get("ref") ?? "";
      const commit = ref === "automation-queue" ? queueHead ?? "" : ref;
      const tree = commits.get(commit)?.tree ?? "";
      const path = decodeURIComponent(url.pathname.split("/contents/")[1] ?? "");
      const blob = trees.get(tree)?.get(path);
      if (!blob) return response({ message: "Not Found" }, 404);
      return new Response(blobs.get(blob) ?? "", { status: 200 });
    }
    return response({ message: `Unhandled ${method} ${url.pathname}` }, 500);
  };

  return {
    fetchImplementation,
    synchronizeNextPatches(count: number) {
      let release: () => void = () => {};
      const promise = new Promise<void>((resolve) => {
        release = resolve;
      });
      patchBarrier = { remaining: count, promise, release };
    },
    latestState: () => {
      const tree = commits.get(queueHead ?? "")?.tree ?? "";
      const blob = trees.get(tree)?.get("runtime/submission-queue.json");
      return blob ? blobs.get(blob) ?? "" : "";
    },
    latestPath: (path: string) => {
      const tree = commits.get(queueHead ?? "")?.tree ?? "";
      const blob = trees.get(tree)?.get(path);
      return blob ? blobs.get(blob) ?? "" : "";
    },
    requestCount: () => requestCount,
  };
}

describe("durable formal verification queue", () => {
  it("admits one active job and preserves FIFO order", () => {
    let state = createEmptyQueueState("2026-08-11");
    const first = enqueueQueueState(
      state,
      input(1),
      "Example-Solver",
      ownerSecret,
      firstDay,
    );
    state = first.state;
    expect(first.result).toMatchObject({
      position: 0,
      dailyUsed: 1,
      dailyLimit: MAX_DAILY_SUBMISSIONS,
      shouldStart: true,
    });

    const second = enqueueQueueState(
      state,
      input(2),
      "another-solver",
      ownerSecret,
      firstDay,
    );
    state = second.state;
    const third = enqueueQueueState(
      state,
      input(3),
      "third-solver",
      ownerSecret,
      firstDay,
    );
    state = third.state;

    expect(second.result).toMatchObject({ position: 1, shouldStart: false });
    expect(third.result).toMatchObject({ position: 2, shouldStart: false });
    expect(inspectQueueState(state, input(2).jobId)).toMatchObject({
      status: "queued",
      position: 1,
    });
    expect(
      inspectOwnerQueueState(state, "ANOTHER-SOLVER", ownerSecret),
    ).toMatchObject({
      status: "queued",
      position: 1,
      job: { jobId: input(2).jobId },
    });
    expect(
      inspectOwnerQueueState(state, "missing-solver", ownerSecret),
    ).toEqual({ status: "missing" });

    const completion = completeQueueState(
      state,
      input(1).jobId,
      {
        outcome: "rejected",
        promotionStatus: null,
        message: "Lean could not elaborate the proof.",
        feedback: {
          code: "lean-elaboration-failed",
          stage: "lean-compilation",
          title: "Lean could not elaborate the proof",
          detail: "Lean found a type or elaboration error.",
          action: "Fix the first Lean error and submit again.",
          retryable: false,
        },
        evidenceUrl: null,
      },
      firstDay,
    );
    expect(completion.result).toMatchObject({
      advanced: true,
      next: { jobId: input(2).jobId },
      receipt: { outcome: "rejected" },
    });
    expect(inspectQueueState(completion.state, input(2).jobId).status).toBe(
      "active",
    );
    expect(inspectQueueState(completion.state, input(1).jobId)).toMatchObject({
      status: "completed",
      receipt: {
        outcome: "rejected",
        feedback: {
          code: "lean-elaboration-failed",
          retryable: false,
        },
      },
    });
  });

  it("enforces three admissions per GitHub account per UTC day", () => {
    let state = createEmptyQueueState("2026-08-11");
    for (let index = 1; index <= MAX_DAILY_SUBMISSIONS; index += 1) {
      const admission = enqueueQueueState(
        state,
        input(index),
        "Rate-Limited-Solver",
        ownerSecret,
        firstDay,
      );
      state = admission.state;
      expect(admission.result.dailyUsed).toBe(index);
    }

    expect(() =>
      enqueueQueueState(
        state,
        input(4),
        "rate-limited-solver",
        ownerSecret,
        firstDay,
      ),
    ).toThrow(DailySubmissionLimitError);

    expect(() =>
      enqueueQueueState(
        state,
        input(5, "record-1"),
        "different-solver",
        ownerSecret,
        firstDay,
      ),
    ).toThrow(SubmissionAlreadyQueuedError);

    expect(() =>
      enqueueQueueState(
        state,
        input(6),
        "different-solver",
        ownerSecret,
        firstDay,
      ),
    ).not.toThrow();
  });

  it("keeps rejected receipts from before structured feedback readable", () => {
    const admission = enqueueQueueState(
      createEmptyQueueState("2026-08-11"),
      input(1),
      "legacy-solver",
      ownerSecret,
      firstDay,
    );
    const completion = completeQueueState(
      admission.state,
      input(1).jobId,
      {
        outcome: "rejected",
        promotionStatus: null,
        message: "The formal verifier exited with status 1.",
        evidenceUrl: null,
      },
      firstDay,
    );

    expect(completion.result.receipt).toMatchObject({
      outcome: "rejected",
      message: "The formal verifier exited with status 1.",
    });
    expect(completion.result.receipt?.feedback).toBeUndefined();
  });

  it("resets admission counts at the UTC day boundary", () => {
    let state = createEmptyQueueState("2026-08-11");
    for (let index = 1; index <= MAX_DAILY_SUBMISSIONS; index += 1) {
      state = enqueueQueueState(
        state,
        input(index),
        "daily-solver",
        ownerSecret,
        firstDay,
      ).state;
    }

    const nextDay = enqueueQueueState(
      state,
      input(10),
      "daily-solver",
      ownerSecret,
      new Date("2026-08-12T00:00:00.000Z"),
    );
    expect(nextDay.result.dailyUsed).toBe(1);
    expect(nextDay.state.daily.day).toBe("2026-08-12");
  });

  it("recovers an active upload without changing its identity or rate limit", () => {
    const admission = enqueueQueueState(
      createEmptyQueueState("2026-08-11"),
      input(1),
      "recovering-solver",
      ownerSecret,
      firstDay,
    );
    const original = admission.result.job;
    const recovered = replaceActiveQueueState(admission.state, original, {
      sandboxId: input(99).sandboxId,
      jobId: input(99).jobId,
      proofDigest: original.proofDigest,
    });

    expect(recovered.result).toMatchObject({
      sandboxId: input(99).sandboxId,
      jobId: input(99).jobId,
      proofDigest: original.proofDigest,
      ownerKey: original.ownerKey,
      submissionKey: original.submissionKey,
      enqueuedAt: original.enqueuedAt,
    });
    expect(recovered.state.daily).toEqual(admission.state.daily);
    expect(recovered.state.pending).toEqual([]);
    expect(recovered.state.completed).toEqual([]);
    expect(() =>
      replaceActiveQueueState(admission.state, original, {
        sandboxId: input(98).sandboxId,
        jobId: input(98).jobId,
        proofDigest: input(98).proofDigest,
      }),
    ).toThrow("preserve the proof digest");
  });

  it("atomically archives encrypted source without publishing identity or plaintext", async () => {
    const github = fakeQueueGitHub();
    const options = {
      token: "test-token",
      ownerSecret,
      archiveKey,
      fetchImplementation: github.fetchImplementation,
      now: firstDay,
    };
    const archived = archivedInput(42, "Visible-Solver", "private-record-name");
    const admission = await enqueueVerificationJob(
      archived.input,
      "Visible-Solver",
      archived.archive,
      options,
    );
    expect(admission).toMatchObject({ position: 0, dailyUsed: 1 });
    const requestsBeforeUsage = github.requestCount();
    await expect(
      getDailySubmissionUsage("visible-solver", options),
    ).resolves.toMatchObject({ used: 1, limit: MAX_DAILY_SUBMISSIONS });
    expect(github.requestCount() - requestsBeforeUsage).toBe(1);

    const ledger = github.latestState();
    expect(ledger).toContain(input(42).jobId);
    expect(ledger).not.toContain("Visible-Solver");
    expect(ledger).not.toContain("visible-solver");
    expect(ledger).not.toContain("private-record-name");
    expect(ledger).not.toContain("Solution.lean");

    const rawArchive = github.latestPath(
      submissionArchivePath(
        archived.input.jobId,
        archived.input.proofDigest,
        firstDay.toISOString(),
      ),
    );
    expect(rawArchive).not.toContain("Visible-Solver");
    expect(rawArchive).not.toContain("private-record-name");
    expect(rawArchive).not.toContain(archived.archive.solution);
    expect(
      openSubmissionArchive(JSON.parse(rawArchive), archiveKey),
    ).toMatchObject({
      jobId: archived.input.jobId,
      proofDigest: archived.input.proofDigest,
      manifest: archived.archive.manifest,
      solution: archived.archive.solution,
    });
  });

  it("serializes concurrent admissions and enforces the daily limit once", async () => {
    const github = fakeQueueGitHub();
    const options = {
      token: "test-token",
      ownerSecret,
      archiveKey,
      fetchImplementation: github.fetchImplementation,
      now: firstDay,
    };
    const first = archivedInput(1, "concurrent-solver");
    await enqueueVerificationJob(
      first.input,
      "concurrent-solver",
      first.archive,
      options,
    );

    github.synchronizeNextPatches(3);
    const candidates = [2, 3, 4].map((index) =>
      archivedInput(index, "CONCURRENT-SOLVER"),
    );
    const results = await Promise.allSettled(
      candidates.map((candidate) =>
        enqueueVerificationJob(
          candidate.input,
          "CONCURRENT-SOLVER",
          candidate.archive,
          options,
        ),
      ),
    );
    const admitted = results.filter(
      (result): result is PromiseFulfilledResult<Awaited<ReturnType<typeof enqueueVerificationJob>>> =>
        result.status === "fulfilled",
    );
    const rejected = results.filter(
      (result): result is PromiseRejectedResult => result.status === "rejected",
    );

    expect(admitted).toHaveLength(2);
    expect(rejected).toHaveLength(1);
    expect(rejected[0].reason).toBeInstanceOf(DailySubmissionLimitError);
    const state = JSON.parse(github.latestState());
    expect(state.active.jobId).toBe(first.input.jobId);
    expect(state.pending).toHaveLength(2);
    expect(new Set(state.pending.map((job: { jobId: string }) => job.jobId))).toEqual(
      new Set(admitted.map((result) => result.value.job.jobId)),
    );
    await expect(
      getDailySubmissionUsage("concurrent-solver", options),
    ).resolves.toMatchObject({ used: MAX_DAILY_SUBMISSIONS });
    for (const result of admitted) {
      expect(
        github.latestPath(
          submissionArchivePath(
            result.value.job.jobId,
            result.value.job.proofDigest,
            firstDay.toISOString(),
          ),
        ),
      ).not.toBe("");
    }
  });
});
