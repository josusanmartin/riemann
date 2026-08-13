import { z } from "zod";
import { githubLoginSchema } from "@/lib/challenge";
import { RECORDS_REPOSITORY } from "@/lib/github-promotion";
import {
  openSubmissionArchive,
  parseSubmissionArchivePath,
  requireSubmissionArchiveKey,
  submissionArchiveEnvelopeSchema,
  summarizeSubmissionArchive,
  type SubmissionArchivePayload,
  type SubmissionArchiveSummary,
} from "@/lib/submission-archive";
import { SUBMISSION_QUEUE_BRANCH } from "@/lib/submission-queue";

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
