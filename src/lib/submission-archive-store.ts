import { isPublicationMismatch } from "./publication-feedback";
import { z } from "zod";
import { isPrivilegedIdentity } from "./privileged-identity";
import { RECORDS_REPOSITORY } from "@/lib/github-promotion";
import {
  openSubmissionArchive,
  openVerifierLog,
  verifierLogPath,
  type VerifierLogPayload,
  parseSubmissionArchivePath,
  requireSubmissionArchiveKey,
  submissionArchiveEnvelopeSchema,
  summarizeSubmissionArchive,
  type SubmissionArchivePayload,
  type SubmissionArchiveSummary,
} from "@/lib/submission-archive";
import { historyOwnerKeys, queueCompletionReceiptSchema, SUBMISSION_QUEUE_BRANCH, SUBMISSION_QUEUE_PATH, submissionQueueStateSchema } from "@/lib/submission-queue";

const GITHUB_API = "https://api.github.com";
const GITHUB_API_VERSION = "2026-03-10";

const shaSchema = z.string().regex(/^[0-9a-f]{40}$/);
const referenceSchema = z
  .object({ object: z.object({ sha: shaSchema }).passthrough() })
  .passthrough();
const commitSchema = z
  .object({ tree: z.object({ sha: shaSchema }).passthrough() })
  .passthrough();
const treeSchema = z
  .object({
    truncated: z.boolean().default(false),
    tree: z.array(
      z
        .object({
          path: z.string(),
          type: z.string(),
          sha: shaSchema,
          size: z.number().int().nonnegative().optional(),
        })
        .passthrough(),
    ),
  })
  .passthrough();
const blobSchema = z
  .object({
    content: z.string(),
    encoding: z.literal("base64"),
  })
  .passthrough();

type FetchImplementation = typeof fetch;

export type SubmissionArchiveStoreOptions = {
  githubId?: string;
  token?: string;
  archiveKey?: string;
  fetchImplementation?: FetchImplementation;
};

export type SubmissionArchiveEntry = {
  path: string;
  blobSha: string;
  encryptedBytes: number;
  jobId: string;
  proofDigest: string;
  submittedAt: string;
};

function requiredToken(options: SubmissionArchiveStoreOptions): string {
  const token = options.token ?? process.env.GITHUB_RECORDS_TOKEN;
  if (!token) throw new Error("The durable submission archive is not configured");
  return token;
}

function repositoryPath(path: string): string {
  return `/repos/${RECORDS_REPOSITORY}/${path}`;
}

class ArchiveGitHubClient {
  constructor(
    private readonly token: string,
    private readonly fetchImplementation: FetchImplementation,
  ) {}

  async json(path: string): Promise<unknown> {
    const response = await this.fetchImplementation(`${GITHUB_API}${path}`, {
      cache: "no-store",
      headers: {
        Accept: "application/vnd.github+json",
        Authorization: `Bearer ${this.token}`,
        "User-Agent": "riemann-fail-archive",
        "X-GitHub-Api-Version": GITHUB_API_VERSION,
      },
    });
    if (!response.ok) {
      const detail = (await response.text()).slice(0, 500).replace(/\s+/g, " ");
      throw new Error(
        `GitHub archive API ${response.status}: ${detail || response.statusText}`,
      );
    }
    return response.json();
  }
}

async function archiveClientAndTree(options: SubmissionArchiveStoreOptions) {
  const client = new ArchiveGitHubClient(
    requiredToken(options),
    options.fetchImplementation ?? fetch,
  );
  const reference = referenceSchema.parse(
    await client.json(
      repositoryPath(`git/ref/heads/${SUBMISSION_QUEUE_BRANCH}`),
    ),
  );
  const commit = commitSchema.parse(
    await client.json(repositoryPath(`git/commits/${reference.object.sha}`)),
  );
  const tree = treeSchema.parse(
    await client.json(
      repositoryPath(`git/trees/${commit.tree.sha}?recursive=1`),
    ),
  );
  if (tree.truncated) {
    throw new Error("GitHub truncated the durable submission archive listing");
  }
  return { client, tree };
}

export function isSubmissionArchiveMaintainer(github: string | undefined, githubId?: string): boolean {
  const admins = process.env.SUBMISSION_ARCHIVE_ADMINS ?? RECORDS_REPOSITORY.split("/")[0];
  return isPrivilegedIdentity(github, githubId, admins);
}

export async function listSubmissionArchive(
  options: SubmissionArchiveStoreOptions = {},
): Promise<SubmissionArchiveEntry[]> {
  const { tree } = await archiveClientAndTree(options);
  return archiveEntries(tree);
}

function archiveEntries(tree: z.infer<typeof treeSchema>): SubmissionArchiveEntry[] {
  return tree.tree
    .filter((entry) => entry.type === "blob")
    .flatMap((entry) => {
      const parsed = parseSubmissionArchivePath(entry.path);
      return parsed
        ? [
            {
              ...parsed,
              blobSha: entry.sha,
              encryptedBytes: entry.size ?? 0,
            },
          ]
        : [];
    })
    .sort((left, right) => right.submittedAt.localeCompare(left.submittedAt));
}

async function readArchiveBlob(
  client: ArchiveGitHubClient,
  entry: SubmissionArchiveEntry,
  encodedKey: string,
): Promise<SubmissionArchivePayload> {
  const blob = blobSchema.parse(
    await client.json(repositoryPath(`git/blobs/${entry.blobSha}`)),
  );
  const raw = Buffer.from(blob.content.replace(/\s+/g, ""), "base64").toString(
    "utf8",
  );
  const envelope = submissionArchiveEnvelopeSchema.parse(JSON.parse(raw));
  const payload = openSubmissionArchive(envelope, encodedKey);
  if (
    payload.jobId !== entry.jobId ||
    payload.proofDigest !== entry.proofDigest ||
    payload.submittedAt !== entry.submittedAt
  ) {
    throw new Error("The archived source does not match its immutable path");
  }
  return payload;
}

export async function readSubmissionArchive(
  jobId: string,
  options: SubmissionArchiveStoreOptions = {},
): Promise<{
  entry: SubmissionArchiveEntry;
  payload: SubmissionArchivePayload;
  summary: SubmissionArchiveSummary;
} | null> {
  const parsedJobId = z.string().uuid().parse(jobId);
  const { client, tree } = await archiveClientAndTree(options);
  const entry = tree.tree
    .filter((candidate) => candidate.type === "blob")
    .flatMap((candidate) => {
      const parsed = parseSubmissionArchivePath(candidate.path);
      return parsed
        ? [
            {
              ...parsed,
              blobSha: candidate.sha,
              encryptedBytes: candidate.size ?? 0,
            },
          ]
        : [];
    })
    .find((candidate) => candidate.jobId === parsedJobId);
  if (!entry) return null;
  const payload = await readArchiveBlob(
    client,
    entry,
    options.archiveKey ?? requireSubmissionArchiveKey(),
  );
  return { entry, payload, summary: summarizeSubmissionArchive(payload) };
}

/** The retained, decrypted verifier log for a job, or null if none was kept. */
export async function readVerifierLog(
  jobId: string,
  proofDigest: string | null,
  options: SubmissionArchiveStoreOptions = {},
): Promise<VerifierLogPayload | null> {
  const path = verifierLogPath(jobId);
  const { client, tree } = await archiveClientAndTree(options);
  const entry = tree.tree.find((candidate) => candidate.type === "blob" && candidate.path === path);
  if (!entry) return null;
  const blob = blobSchema.parse(await client.json(repositoryPath(`git/blobs/${entry.sha}`)));
  const envelope = JSON.parse(
    Buffer.from(blob.content.replace(/\s+/g, ""), "base64").toString("utf8"),
  ) as unknown;
  const payload = openVerifierLog(envelope, options.archiveKey ?? requireSubmissionArchiveKey());
  // The digest is bound into the ciphertext; also bind it to the caller's job.
  if (payload.jobId !== jobId || (proofDigest !== null && payload.proofDigest !== proofDigest)) {
    throw new Error("The retained verifier log belongs to a different job");
  }
  return payload;
}

/** Scope the index to the authenticated login before resolving any requested attempt or log. */
export async function readOwnerHistory(github: string, selectedId?: string, options: SubmissionArchiveStoreOptions = {}) {
  const owners = historyOwnerKeys(github, options.githubId);
  const prefixes = owners.map(owner => `runtime/history/${owner}/`);
  const { client, tree } = await archiveClientAndTree(options);
  async function jsonBlob(sha: string) {
    const blob = blobSchema.parse(await client.json(repositoryPath(`git/blobs/${sha}`)));
    return JSON.parse(Buffer.from(blob.content, "base64").toString("utf8"));
  }
  const completed = tree.tree.filter(entry => entry.type === "blob" && prefixes.some(prefix => entry.path.startsWith(prefix)))
    .map(entry => {
      const [date, status, digest, jobId] = entry.path.slice(prefixes[0].length, -5).split("_");
      return { date, status, digest, jobId, sha: entry.sha };
    }).sort((a, b) => b.date.localeCompare(a.date));
  const stateEntry = tree.tree.find(entry => entry.path === SUBMISSION_QUEUE_PATH);
  if (!stateEntry) throw new Error("Submission queue state unavailable");
  const state = submissionQueueStateSchema.parse(await jsonBlob(stateEntry.sha));
  const blocked = new Set(state.completed.filter(receipt => isPublicationMismatch(receipt.message)).map(receipt => receipt.jobId));
  for (const row of completed) {
    if (row.status === "superseded" && blocked.has(row.jobId)) row.status = "publication-blocked";
  }
  const active = [state.active, ...state.pending].flatMap((job, index) => {
    if (!job || !owners.includes(job.ownerKey)) return [];
    const status = index ? "Queued" : !job.boat ? "In progress" : job.boat.uploaded
      ? "Verifying" : job.boat.workerId ? "Transferring files" : "Requesting worker";
    return [{ jobId: job.jobId, date: job.enqueuedAt, digest: job.proofDigest, status }];
  });
  const selected = completed.find(row => row.jobId === selectedId);
  if (!selected) return { active, completed, detail: null };
  const receipt = queueCompletionReceiptSchema.parse(await jsonBlob(selected.sha));
  if (receipt.jobId !== selected.jobId || receipt.proofDigest !== selected.digest)
    throw new Error("Attempt history identity mismatch");
  const logIds = [receipt.firstAttemptLogId, receipt.logArchived ? receipt.jobId : undefined];
  const attempts = await Promise.allSettled(logIds.flatMap(id => id ? [id] : []).map(async id => {
    const entry = tree.tree.find(item => item.path === verifierLogPath(id));
    if (!entry) return null;
    const log = openVerifierLog(await jsonBlob(entry.sha), options.archiveKey ?? requireSubmissionArchiveKey());
    if (log.jobId !== id || log.proofDigest !== receipt.proofDigest) throw new Error("Attempt log identity mismatch");
    return log;
  }));
  const unavailable = attempts.some(attempt => attempt.status === "rejected" || attempt.value === null);
  if (unavailable) console.warn("Attempt has an unavailable log", { jobId: receipt.jobId });
  const logs = attempts.flatMap(attempt => attempt.status === "fulfilled" && attempt.value?.log ? [attempt.value] : []);
  return { active, completed, detail: { receipt, logs, unavailable } };
}

type DeskRow = {
  jobId: string; digest: string; date: string; status: string;
  sourceId?: string; hasLog?: boolean; message?: string; evidenceUrl?: string;
};

/** Read only archive indexes and queue metadata. Source and log blobs are opened on demand. */
export async function readVerificationDesk(login: string, githubId: string | undefined, options: SubmissionArchiveStoreOptions = {}) {
  if (!isSubmissionArchiveMaintainer(login, githubId)) throw new Error("Maintainer access required");
  const { client, tree } = await archiveClientAndTree(options);
  const queue = tree.tree.find(e => e.path === SUBMISSION_QUEUE_PATH && e.type === "blob");
  if (!queue) throw new Error("Queue state unavailable");
  const blob = blobSchema.parse(await client.json(repositoryPath(`git/blobs/${queue.sha}`)));
  const state = submissionQueueStateSchema.parse(JSON.parse(Buffer.from(blob.content, "base64").toString("utf8")));
  const sources = archiveEntries(tree);
  const sourceByDigest = new Map(sources.map(e => [e.proofDigest, e.jobId]));
  const rows = new Map<string, DeskRow>(sources.map(e => [e.jobId, {
    jobId: e.jobId, digest: e.proofDigest, date: e.submittedAt, status: "archived", sourceId: e.jobId,
  }]));
  const paths = new Set(tree.tree.map(e => e.path));
  for (const entry of tree.tree) {
    if (entry.type !== "blob" || !entry.path.startsWith("runtime/history/")) continue;
    const [date, status, digest, jobId] = entry.path.split("/").at(-1)!.replace(/\.json$/, "").split("_");
    if (!jobId || !/^[0-9a-f]{64}$/.test(digest)) continue;
    const source = rows.get(jobId);
    rows.set(jobId, { jobId, digest, date: source?.date ?? date, status, sourceId: source?.sourceId ?? sourceByDigest.get(digest), hasLog: paths.has(verifierLogPath(jobId)) });
  }
  for (const receipt of state.completed) {
    const row = rows.get(receipt.jobId);
    rows.set(receipt.jobId, {
      jobId: receipt.jobId, digest: receipt.proofDigest, date: row?.date ?? receipt.completedAt,
      status: isPublicationMismatch(receipt.message) ? "publication-blocked" : receipt.outcome,
      sourceId: row?.sourceId ?? sourceByDigest.get(receipt.proofDigest),
      hasLog: receipt.logArchived || row?.hasLog, message: receipt.feedback?.title ?? receipt.message ?? undefined,
      evidenceUrl: receipt.evidenceUrl ?? undefined,
    });
  }
  const live = [state.active, ...state.pending].flatMap((job, i) => {
    if (!job) return [];
    const status = i ? "Queued" : job.boat?.uploaded ? "Verifying" : job.boat?.workerId ? "Transferring files" : "Starting";
    const row = { jobId: job.jobId, digest: job.proofDigest, date: job.enqueuedAt, status,
      sourceId: rows.get(job.jobId)?.sourceId ?? sourceByDigest.get(job.proofDigest) };
    rows.delete(job.jobId);
    return [row];
  });
  return { live, attempts: [...rows.values()].sort((a,b) => b.date.localeCompare(a.date)), sources: sources.length, waiting: state.pending.length, active: Number(Boolean(state.active)) };
}
