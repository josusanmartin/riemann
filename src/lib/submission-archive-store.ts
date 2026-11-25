import { z } from "zod";
import { githubLoginSchema } from "@/lib/challenge";
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
import { historyOwnerKey, queueCompletionReceiptSchema, SUBMISSION_QUEUE_BRANCH, SUBMISSION_QUEUE_PATH, submissionQueueStateSchema } from "@/lib/submission-queue";

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

export function isSubmissionArchiveMaintainer(github: string | undefined): boolean {
  if (!github) return false;
  let login: string;
  try {
    login = githubLoginSchema.parse(github).toLowerCase();
  } catch {
    return false;
  }
  const configured = process.env.SUBMISSION_ARCHIVE_ADMINS;
  const rawAdmins = configured
    ? configured.split(",").map((value) => value.trim()).filter(Boolean)
    : [RECORDS_REPOSITORY.split("/")[0]];
  try {
    return rawAdmins
      .map((value) => githubLoginSchema.parse(value).toLowerCase())
      .includes(login);
  } catch {
    return false;
  }
}

export async function listSubmissionArchive(
  options: SubmissionArchiveStoreOptions = {},
): Promise<SubmissionArchiveEntry[]> {
  const { tree } = await archiveClientAndTree(options);
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
  const owner = historyOwnerKey(github);
  const prefix = `runtime/history/${owner}/`;
  const { client, tree } = await archiveClientAndTree(options);
  async function jsonBlob(sha: string) {
    const blob = blobSchema.parse(await client.json(repositoryPath(`git/blobs/${sha}`)));
    return JSON.parse(Buffer.from(blob.content, "base64").toString("utf8"));
  }
  const completed = tree.tree.filter(entry => entry.type === "blob" && entry.path.startsWith(prefix))
    .map(entry => {
      const [date, status, digest, jobId] = entry.path.slice(prefix.length, -5).split("_");
      return { date, status, digest, jobId, sha: entry.sha };
    }).sort((a, b) => b.date.localeCompare(a.date));
  const stateEntry = tree.tree.find(entry => entry.path === SUBMISSION_QUEUE_PATH);
  if (!stateEntry) throw new Error("Submission queue state unavailable");
  const state = submissionQueueStateSchema.parse(await jsonBlob(stateEntry.sha));
  const active = [state.active, ...state.pending].flatMap((job, index) => {
    if (!job || job.ownerKey !== owner) return [];
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
  const logs = await Promise.all(logIds.flatMap(id => id ? [id] : []).map(async id => {
    const entry = tree.tree.find(item => item.path === verifierLogPath(id));
    if (!entry) return null;
    const log = openVerifierLog(await jsonBlob(entry.sha), options.archiveKey ?? requireSubmissionArchiveKey());
    if (log.jobId !== id || log.proofDigest !== receipt.proofDigest) throw new Error("Attempt log identity mismatch");
    return log;
  }));
  return { active, completed, detail: { receipt, logs: logs.filter((log): log is VerifierLogPayload => log !== null && log.log.length > 0) } };
}
