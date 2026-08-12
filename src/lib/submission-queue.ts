import { createHmac } from "node:crypto";
import { z } from "zod";
import { githubLoginSchema } from "@/lib/challenge";
import { RECORDS_BRANCH, RECORDS_REPOSITORY } from "@/lib/github-promotion";
import { verifierFeedbackSchema } from "@/lib/verifier-feedback";

const GITHUB_API = "https://api.github.com";
const GITHUB_API_VERSION = "2026-03-10";
export const SUBMISSION_QUEUE_BRANCH = "automation-queue";
export const SUBMISSION_QUEUE_PATH = "runtime/submission-queue.json";
export const MAX_DAILY_SUBMISSIONS = 3;
export const MAX_QUEUED_SUBMISSIONS = 100;
export const MAX_COMPLETED_RECEIPTS = 200;
const MAX_CAS_ATTEMPTS = 8;

const shaSchema = z.string().regex(/^[0-9a-f]{40}$/);
const digestSchema = z.string().regex(/^[0-9a-f]{64}$/);
const sandboxIdSchema = z
  .string()
  .min(10)
  .max(160)
  .regex(/^[A-Za-z0-9-]+$/);
const utcDaySchema = z.string().regex(/^\d{4}-\d{2}-\d{2}$/);

export const queuedVerificationJobSchema = z
  .object({
    sandboxId: sandboxIdSchema,
    jobId: z.string().uuid(),
    proofDigest: digestSchema,
    ownerKey: digestSchema,
    submissionKey: digestSchema,
    enqueuedAt: z.string().datetime({ offset: true }),
  })
  .strict();

export const queueCompletionReceiptSchema = z
  .object({
    jobId: z.string().uuid(),
    proofDigest: digestSchema,
    outcome: z.enum(["rejected", "promoted", "superseded"]),
    promotionStatus: z.enum(["promoted", "already-promoted"]).nullable(),
    message: z.string().min(1).max(2_000).nullable(),
    feedback: verifierFeedbackSchema.optional(),
    evidenceUrl: z.url().max(1_000).nullable(),
    completedAt: z.string().datetime({ offset: true }),
  })
  .strict()
  .superRefine((receipt, context) => {
    if (receipt.outcome === "promoted" && !receipt.promotionStatus) {
      context.addIssue({
        code: "custom",
        message: "Promoted queue receipts require a promotion status",
      });
    }
    if (receipt.outcome !== "promoted" && receipt.promotionStatus) {
      context.addIssue({
        code: "custom",
        message: "Only promoted queue receipts may have a promotion status",
      });
    }
    if (receipt.outcome !== "rejected" && receipt.feedback) {
      context.addIssue({
        code: "custom",
        message: "Only rejected queue receipts may include verifier feedback",
      });
    }
  });

export const submissionQueueStateSchema = z
  .object({
    schemaVersion: z.literal(1),
    active: queuedVerificationJobSchema.nullable(),
    pending: z.array(queuedVerificationJobSchema).max(MAX_QUEUED_SUBMISSIONS),
    completed: z.array(queueCompletionReceiptSchema).max(MAX_COMPLETED_RECEIPTS),
    daily: z
      .object({
        day: utcDaySchema,
        attempts: z.record(digestSchema, z.number().int().min(0).max(MAX_DAILY_SUBMISSIONS)),
      })
      .strict(),
  })
  .strict()
  .superRefine((state, context) => {
    const jobs = state.active ? [state.active, ...state.pending] : state.pending;
    if (jobs.length > MAX_QUEUED_SUBMISSIONS) {
      context.addIssue({
        code: "custom",
        message: "The formal verification queue exceeds its capacity",
      });
    }
    const jobIds = new Set<string>();
    const sandboxIds = new Set<string>();
    const submissionKeys = new Set<string>();
    for (const job of jobs) {
      if (jobIds.has(job.jobId)) {
        context.addIssue({ code: "custom", message: "Queue job IDs must be unique" });
      }
      if (sandboxIds.has(job.sandboxId)) {
        context.addIssue({ code: "custom", message: "Queue sandbox IDs must be unique" });
      }
      if (submissionKeys.has(job.submissionKey)) {
        context.addIssue({ code: "custom", message: "Queued record names must be unique" });
      }
      jobIds.add(job.jobId);
      sandboxIds.add(job.sandboxId);
      submissionKeys.add(job.submissionKey);
    }
    const completedIds = new Set<string>();
    for (const receipt of state.completed) {
      if (jobIds.has(receipt.jobId) || completedIds.has(receipt.jobId)) {
        context.addIssue({ code: "custom", message: "Queue receipt IDs must be unique" });
      }
      completedIds.add(receipt.jobId);
    }
  });

export type QueuedVerificationJob = z.infer<typeof queuedVerificationJobSchema>;
export type QueueCompletionReceipt = z.infer<typeof queueCompletionReceiptSchema>;
export type SubmissionQueueState = z.infer<typeof submissionQueueStateSchema>;

export type QueueJobInput = {
  sandboxId: string;
  jobId: string;
  proofDigest: string;
  submissionId: string;
};

export type ActiveQueueJobReplacement = Pick<
  QueueJobInput,
  "sandboxId" | "jobId" | "proofDigest"
>;

export type QueueAdmission = {
  job: QueuedVerificationJob;
  position: number;
  dailyUsed: number;
  dailyLimit: number;
  shouldStart: boolean;
};

export type QueueInspection =
  | { status: "active"; position: 0; job: QueuedVerificationJob }
  | { status: "queued"; position: number; job: QueuedVerificationJob }
  | { status: "completed"; receipt: QueueCompletionReceipt }
  | { status: "missing" };

export type OwnerQueueInspection =
  | { status: "active"; position: 0; job: QueuedVerificationJob }
  | { status: "queued"; position: number; job: QueuedVerificationJob }
  | { status: "missing" };

export type QueueAdvance = {
  advanced: boolean;
  next: QueuedVerificationJob | null;
  receipt: QueueCompletionReceipt | null;
};

export type QueueCompletionInput = Omit<
  QueueCompletionReceipt,
  "jobId" | "proofDigest" | "completedAt"
> & { completedAt?: string };

type FetchImplementation = typeof fetch;
type QueueOptions = {
  token?: string;
  ownerSecret?: string;
  fetchImplementation?: FetchImplementation;
  now?: Date;
};

type QueueMutation<T> = {
  state: SubmissionQueueState;
  result: T;
  changed: boolean;
};

export class DailySubmissionLimitError extends Error {
  readonly limit = MAX_DAILY_SUBMISSIONS;

  constructor(public readonly retryAt: string) {
    super(`Each GitHub account may submit at most ${MAX_DAILY_SUBMISSIONS} proofs per UTC day`);
    this.name = "DailySubmissionLimitError";
  }
}

export class SubmissionQueueFullError extends Error {
  constructor() {
    super("The formal verification queue is currently full");
    this.name = "SubmissionQueueFullError";
  }
}

export class SubmissionAlreadyQueuedError extends Error {
  constructor() {
    super("That record name is already queued for verification");
    this.name = "SubmissionAlreadyQueuedError";
  }
}

class QueueGitHubError extends Error {
  constructor(
    message: string,
    public readonly status: number,
  ) {
    super(message);
    this.name = "QueueGitHubError";
  }
}

const objectShaSchema = z.object({ sha: shaSchema }).passthrough();
const referenceSchema = z.object({ object: objectShaSchema }).passthrough();
const commitSchema = z
  .object({ sha: shaSchema, tree: objectShaSchema })
  .passthrough();

function utcDay(now: Date): string {
  return now.toISOString().slice(0, 10);
}

function nextUtcDay(now: Date): string {
  const next = new Date(Date.UTC(
    now.getUTCFullYear(),
    now.getUTCMonth(),
    now.getUTCDate() + 1,
  ));
  return next.toISOString();
}

function hmacKey(kind: "owner" | "submission", value: string, secret: string): string {
  return createHmac("sha256", secret)
    .update(`riemann-fail-queue-${kind}-v1\0`)
    .update(value.toLowerCase())
    .digest("hex");
}

export function createEmptyQueueState(day: string): SubmissionQueueState {
  return submissionQueueStateSchema.parse({
    schemaVersion: 1,
    active: null,
    pending: [],
    completed: [],
    daily: { day, attempts: {} },
  });
}

function copyForDay(state: SubmissionQueueState, day: string): SubmissionQueueState {
  return {
    schemaVersion: 1,
    active: state.active ? { ...state.active } : null,
    pending: state.pending.map((job) => ({ ...job })),
    completed: state.completed.map((receipt) => ({ ...receipt })),
    daily:
      state.daily.day === day
        ? { day, attempts: { ...state.daily.attempts } }
        : { day, attempts: {} },
  };
}

export function enqueueQueueState(
  state: SubmissionQueueState,
  input: QueueJobInput,
  github: string,
  ownerSecret: string,
  now: Date,
): QueueMutation<QueueAdmission> {
  const parsedState = submissionQueueStateSchema.parse(state);
  const login = githubLoginSchema.parse(github).toLowerCase();
  const day = utcDay(now);
  const next = copyForDay(parsedState, day);
  const ownerKey = hmacKey("owner", login, ownerSecret);
  const submissionKey = hmacKey("submission", input.submissionId, ownerSecret);
  const existingJobs = next.active ? [next.active, ...next.pending] : next.pending;
  const existing = existingJobs.find((job) => job.jobId === input.jobId);
  const used = next.daily.attempts[ownerKey] ?? 0;
  if (existing) {
    const active = next.active?.jobId === existing.jobId;
    return {
      state: next,
      changed: false,
      result: {
        job: existing,
        position: active
          ? 0
          : next.pending.findIndex((job) => job.jobId === existing.jobId) + 1,
        dailyUsed: used,
        dailyLimit: MAX_DAILY_SUBMISSIONS,
        shouldStart: false,
      },
    };
  }
  if (existingJobs.some((job) => job.submissionKey === submissionKey)) {
    throw new SubmissionAlreadyQueuedError();
  }
  if (used >= MAX_DAILY_SUBMISSIONS) {
    throw new DailySubmissionLimitError(nextUtcDay(now));
  }
  if (existingJobs.length >= MAX_QUEUED_SUBMISSIONS) {
    throw new SubmissionQueueFullError();
  }

  const job = queuedVerificationJobSchema.parse({
    sandboxId: input.sandboxId,
    jobId: input.jobId,
    proofDigest: input.proofDigest,
    ownerKey,
    submissionKey,
    enqueuedAt: now.toISOString(),
  });
  next.daily.attempts[ownerKey] = used + 1;
  let position: number;
  let shouldStart = false;
  if (next.active) {
    next.pending.push(job);
    position = next.pending.length;
  } else {
    next.active = job;
    position = 0;
    shouldStart = true;
  }
  return {
    state: submissionQueueStateSchema.parse(next),
    changed: true,
    result: {
      job,
      position,
      dailyUsed: used + 1,
      dailyLimit: MAX_DAILY_SUBMISSIONS,
      shouldStart,
    },
  };
}

export function completeQueueState(
  state: SubmissionQueueState,
  jobId: string,
  completion: QueueCompletionInput,
  now = new Date(),
): QueueMutation<QueueAdvance> {
  const parsed = submissionQueueStateSchema.parse(state);
  const existingReceipt = parsed.completed.find((receipt) => receipt.jobId === jobId);
  if (existingReceipt) {
    return {
      state: parsed,
      changed: false,
      result: { advanced: false, next: parsed.active, receipt: existingReceipt },
    };
  }
  if (parsed.active?.jobId !== jobId) {
    return {
      state: parsed,
      changed: false,
      result: { advanced: false, next: parsed.active, receipt: null },
    };
  }
  const receipt = queueCompletionReceiptSchema.parse({
    ...completion,
    jobId,
    proofDigest: parsed.active.proofDigest,
    completedAt: completion.completedAt ?? now.toISOString(),
  });
  const pending = [...parsed.pending];
  const next = pending.shift() ?? null;
  const updated = submissionQueueStateSchema.parse({
    ...parsed,
    active: next,
    pending,
    completed: [receipt, ...parsed.completed].slice(0, MAX_COMPLETED_RECEIPTS),
  });
  return {
    state: updated,
    changed: true,
    result: { advanced: true, next, receipt },
  };
}

export function replaceActiveQueueState(
  state: SubmissionQueueState,
  expected: QueuedVerificationJob,
  replacement: ActiveQueueJobReplacement,
): QueueMutation<QueuedVerificationJob> {
  const parsed = submissionQueueStateSchema.parse(state);
  if (
    !parsed.active ||
    parsed.active.sandboxId !== expected.sandboxId ||
    parsed.active.jobId !== expected.jobId ||
    parsed.active.proofDigest !== expected.proofDigest ||
    parsed.active.ownerKey !== expected.ownerKey ||
    parsed.active.submissionKey !== expected.submissionKey
  ) {
    throw new Error("The active verification job changed before recovery");
  }
  if (replacement.proofDigest !== expected.proofDigest) {
    throw new Error("A recovered verification job must preserve the proof digest");
  }

  const recovered = queuedVerificationJobSchema.parse({
    ...expected,
    sandboxId: replacement.sandboxId,
    jobId: replacement.jobId,
    proofDigest: replacement.proofDigest,
  });
  return {
    state: submissionQueueStateSchema.parse({ ...parsed, active: recovered }),
    result: recovered,
    changed: true,
  };
}

export function inspectQueueState(
  state: SubmissionQueueState,
  jobId: string,
): QueueInspection {
  const parsed = submissionQueueStateSchema.parse(state);
  if (parsed.active?.jobId === jobId) {
    return { status: "active", position: 0, job: parsed.active };
  }
  const index = parsed.pending.findIndex((job) => job.jobId === jobId);
  if (index >= 0) {
    return { status: "queued", position: index + 1, job: parsed.pending[index] };
  }
  const receipt = parsed.completed.find((item) => item.jobId === jobId);
  return receipt ? { status: "completed", receipt } : { status: "missing" };
}

export function inspectOwnerQueueState(
  state: SubmissionQueueState,
  github: string,
  ownerSecret: string,
): OwnerQueueInspection {
  const parsed = submissionQueueStateSchema.parse(state);
  const ownerKey = hmacKey(
    "owner",
    githubLoginSchema.parse(github),
    ownerSecret,
  );
  if (parsed.active?.ownerKey === ownerKey) {
    return { status: "active", position: 0, job: parsed.active };
  }
  const index = parsed.pending.findIndex((job) => job.ownerKey === ownerKey);
  return index >= 0
    ? { status: "queued", position: index + 1, job: parsed.pending[index] }
    : { status: "missing" };
}

function requiredToken(options: QueueOptions): string {
  const token = options.token ?? process.env.GITHUB_RECORDS_TOKEN;
  if (!token) throw new Error("The durable submission queue is not configured");
  return token;
}

function requiredOwnerSecret(options: QueueOptions): string {
  const secret = options.ownerSecret ?? process.env.AUTH_SECRET;
  if (!secret) throw new Error("The durable submission queue owner key is not configured");
  return secret;
}

class QueueGitHubClient {
  constructor(
    private readonly token: string,
    private readonly fetchImplementation: FetchImplementation,
  ) {}

  async request(
    path: string,
    init: RequestInit = {},
    allowedStatuses: number[] = [],
  ): Promise<Response> {
    const response = await this.fetchImplementation(`${GITHUB_API}${path}`, {
      ...init,
      cache: "no-store",
      headers: {
        Accept: "application/vnd.github+json",
        Authorization: `Bearer ${this.token}`,
        "Content-Type": "application/json",
        "User-Agent": "riemann-fail-queue",
        "X-GitHub-Api-Version": GITHUB_API_VERSION,
        ...init.headers,
      },
    });
    if (!response.ok && !allowedStatuses.includes(response.status)) {
      const detail = (await response.text()).slice(0, 500).replace(/\s+/g, " ");
      throw new QueueGitHubError(
        `GitHub queue API ${response.status}: ${detail || response.statusText}`,
        response.status,
      );
    }
    return response;
  }

  async json(path: string, init: RequestInit = {}): Promise<unknown> {
    return (await this.request(path, init)).json();
  }
}

function repositoryPath(path: string): string {
  return `/repos/${RECORDS_REPOSITORY}/${path}`;
}

async function getRef(
  client: QueueGitHubClient,
  branch: string,
): Promise<string | null> {
  const response = await client.request(
    repositoryPath(`git/ref/heads/${branch}`),
    {},
    [404],
  );
  if (response.status === 404) return null;
  return referenceSchema.parse(await response.json()).object.sha;
}

async function getCommit(client: QueueGitHubClient, sha: string) {
  return commitSchema.parse(
    await client.json(repositoryPath(`git/commits/${sha}`)),
  );
}

async function readState(
  client: QueueGitHubClient,
  head: string,
): Promise<SubmissionQueueState> {
  const response = await client.request(
    repositoryPath(
      `contents/${SUBMISSION_QUEUE_PATH}?ref=${encodeURIComponent(head)}`,
    ),
    { headers: { Accept: "application/vnd.github.raw+json" } },
  );
  return submissionQueueStateSchema.parse(JSON.parse(await response.text()));
}

async function createBlob(client: QueueGitHubClient, content: string): Promise<string> {
  return objectShaSchema.parse(
    await client.json(repositoryPath("git/blobs"), {
      method: "POST",
      body: JSON.stringify({ content, encoding: "utf-8" }),
    }),
  ).sha;
}

async function createTree(
  client: QueueGitHubClient,
  baseTree: string,
  blob: string,
): Promise<string> {
  return objectShaSchema.parse(
    await client.json(repositoryPath("git/trees"), {
      method: "POST",
      body: JSON.stringify({
        base_tree: baseTree,
        tree: [
          {
            path: SUBMISSION_QUEUE_PATH,
            mode: "100644",
            type: "blob",
            sha: blob,
          },
        ],
      }),
    }),
  ).sha;
}

async function createCommit(
  client: QueueGitHubClient,
  tree: string,
  parent: string,
  message: string,
  now: Date,
): Promise<string> {
  const identity = {
    name: "Riemann.fail Queue",
    email: "queue@riemann.fail",
    date: now.toISOString(),
  };
  return objectShaSchema.parse(
    await client.json(repositoryPath("git/commits"), {
      method: "POST",
      body: JSON.stringify({
        message,
        tree,
        parents: [parent],
        author: identity,
        committer: identity,
      }),
    }),
  ).sha;
}

async function writeStateCommit(
  client: QueueGitHubClient,
  head: string,
  state: SubmissionQueueState,
  message: string,
  now: Date,
): Promise<string> {
  const commit = await getCommit(client, head);
  const blob = await createBlob(client, `${JSON.stringify(state, null, 2)}\n`);
  const tree = await createTree(client, commit.tree.sha, blob);
  return createCommit(client, tree, head, message, now);
}

async function initializeQueue(
  client: QueueGitHubClient,
  now: Date,
): Promise<string> {
  const main = await getRef(client, RECORDS_BRANCH);
  if (!main) throw new Error("The records branch is unavailable");
  const initial = createEmptyQueueState(utcDay(now));
  const commit = await writeStateCommit(
    client,
    main,
    initial,
    "queue: initialize durable submission FIFO",
    now,
  );
  try {
    await client.json(repositoryPath("git/refs"), {
      method: "POST",
      body: JSON.stringify({
        ref: `refs/heads/${SUBMISSION_QUEUE_BRANCH}`,
        sha: commit,
      }),
    });
    return commit;
  } catch (error) {
    if (error instanceof QueueGitHubError && error.status === 422) {
      const raced = await getRef(client, SUBMISSION_QUEUE_BRANCH);
      if (raced) return raced;
    }
    throw error;
  }
}

async function queueHead(
  client: QueueGitHubClient,
  now: Date,
  initialize: boolean,
): Promise<string | null> {
  return (
    (await getRef(client, SUBMISSION_QUEUE_BRANCH)) ??
    (initialize ? await initializeQueue(client, now) : null)
  );
}

async function mutateQueue<T>(
  options: QueueOptions,
  message: string,
  mutate: (state: SubmissionQueueState) => QueueMutation<T>,
): Promise<T> {
  const now = options.now ?? new Date();
  const client = new QueueGitHubClient(
    requiredToken(options),
    options.fetchImplementation ?? fetch,
  );
  for (let attempt = 0; attempt < MAX_CAS_ATTEMPTS; attempt += 1) {
    const head = await queueHead(client, now, true);
    if (!head) throw new Error("The durable submission queue is unavailable");
    const mutation = mutate(await readState(client, head));
    if (!mutation.changed) return mutation.result;
    const commit = await writeStateCommit(client, head, mutation.state, message, now);
    try {
      await client.json(
        repositoryPath(`git/refs/heads/${SUBMISSION_QUEUE_BRANCH}`),
        {
          method: "PATCH",
          body: JSON.stringify({ sha: commit, force: false }),
        },
      );
      return mutation.result;
    } catch (error) {
      if (
        error instanceof QueueGitHubError &&
        (error.status === 409 || error.status === 422)
      ) {
        continue;
      }
      throw error;
    }
  }
  throw new Error("The durable submission queue changed too many times; retry shortly");
}

export function isSubmissionQueueConfigured(): boolean {
  return Boolean(process.env.GITHUB_RECORDS_TOKEN && process.env.AUTH_SECRET);
}

export async function getDailySubmissionUsage(
  github: string,
  options: QueueOptions = {},
): Promise<{ used: number; limit: number; retryAt: string }> {
  const now = options.now ?? new Date();
  const client = new QueueGitHubClient(
    requiredToken(options),
    options.fetchImplementation ?? fetch,
  );
  const head = await queueHead(client, now, false);
  if (!head) {
    return { used: 0, limit: MAX_DAILY_SUBMISSIONS, retryAt: nextUtcDay(now) };
  }
  const state = await readState(client, head);
  const ownerKey = hmacKey(
    "owner",
    githubLoginSchema.parse(github),
    requiredOwnerSecret(options),
  );
  return {
    used: state.daily.day === utcDay(now) ? state.daily.attempts[ownerKey] ?? 0 : 0,
    limit: MAX_DAILY_SUBMISSIONS,
    retryAt: nextUtcDay(now),
  };
}

export function enqueueVerificationJob(
  input: QueueJobInput,
  github: string,
  options: QueueOptions = {},
): Promise<QueueAdmission> {
  const now = options.now ?? new Date();
  const secret = requiredOwnerSecret(options);
  return mutateQueue(
    { ...options, now },
    "queue: enqueue formal verification",
    (state) => enqueueQueueState(state, input, github, secret, now),
  );
}

export function completeVerificationJob(
  jobId: string,
  completion: QueueCompletionInput,
  options: QueueOptions = {},
): Promise<QueueAdvance> {
  z.string().uuid().parse(jobId);
  const now = options.now ?? new Date();
  return mutateQueue(
    { ...options, now },
    "queue: complete and advance formal verification FIFO",
    (state) => completeQueueState(state, jobId, completion, now),
  );
}

export function replaceActiveVerificationJob(
  expected: QueuedVerificationJob,
  replacement: ActiveQueueJobReplacement,
  options: QueueOptions = {},
): Promise<QueuedVerificationJob> {
  return mutateQueue(
    options,
    "queue: recover active formal verification",
    (state) => replaceActiveQueueState(state, expected, replacement),
  );
}

export async function inspectVerificationJob(
  jobId: string,
  options: QueueOptions = {},
): Promise<QueueInspection> {
  z.string().uuid().parse(jobId);
  const now = options.now ?? new Date();
  const client = new QueueGitHubClient(
    requiredToken(options),
    options.fetchImplementation ?? fetch,
  );
  const head = await queueHead(client, now, false);
  return head
    ? inspectQueueState(await readState(client, head), jobId)
    : { status: "missing" };
}

export async function inspectVerificationJobForOwner(
  github: string,
  options: QueueOptions = {},
): Promise<OwnerQueueInspection> {
  const now = options.now ?? new Date();
  const client = new QueueGitHubClient(
    requiredToken(options),
    options.fetchImplementation ?? fetch,
  );
  const head = await queueHead(client, now, false);
  return head
    ? inspectOwnerQueueState(
        await readState(client, head),
        github,
        requiredOwnerSecret(options),
      )
    : { status: "missing" };
}

export async function getActiveVerificationJob(
  options: QueueOptions = {},
): Promise<QueuedVerificationJob | null> {
  const now = options.now ?? new Date();
  const client = new QueueGitHubClient(
    requiredToken(options),
    options.fetchImplementation ?? fetch,
  );
  const head = await queueHead(client, now, false);
  return head ? (await readState(client, head)).active : null;
}
