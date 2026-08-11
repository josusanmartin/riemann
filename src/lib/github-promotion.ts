import { ZodError, z } from "zod";
import contractJson from "../../challenge/contract.json";
import {
  compareRationals,
  contractSchema,
  gitShaSchema,
  rationalToDecimal,
  recordsSchema,
  submissionSchema,
  type RecordEntry,
  type Submission,
  type VerificationAttestation,
} from "@/lib/challenge";
import { assertValidAttestation } from "@/lib/attestation";
import { computeDirectProofDigest } from "@/lib/direct-submission";
import type { E2BVerificationResult } from "@/lib/e2b-verifier";
import {
  computeTrustedMaterialDigest,
  computeVerifierTemplateDigest,
} from "../../scripts/trusted-material";

const GITHUB_API = "https://api.github.com";
const GITHUB_API_VERSION = "2026-03-10";
export const RECORDS_REPOSITORY = "josusanmartin/riemann";
export const RECORDS_BRANCH = "main";

const objectShaSchema = z.object({ sha: gitShaSchema }).passthrough();
const referenceSchema = z
  .object({ object: objectShaSchema })
  .passthrough();
const commitSchema = z
  .object({ sha: gitShaSchema, tree: objectShaSchema })
  .passthrough();

type VerifiedResult = Extract<E2BVerificationResult, { status: "verified" }>;
type FetchImplementation = typeof fetch;

export type VerifiedPromotionInput = {
  baseCommitSha: string;
  previousRecordId: string;
  proofDigest: string;
  issuedAt: number;
  manifest: string;
  solution: string;
  result: VerifiedResult;
};

export type PromotionResult = {
  status: "promoted" | "already-promoted";
  recordId: string;
  evidenceCommitSha: string;
  promotionCommitSha: string;
  evidenceUrl: string;
};

export class PromotionRaceError extends Error {
  constructor(message = "The public record changed while this proof was being verified") {
    super(message);
    this.name = "PromotionRaceError";
  }
}

export class GitHubPromotionError extends Error {
  constructor(
    message: string,
    public readonly status: number,
  ) {
    super(message);
    this.name = "GitHubPromotionError";
  }
}

export function isGitHubPromotionConfigured(): boolean {
  return Boolean(process.env.GITHUB_RECORDS_TOKEN);
}

function requireToken(): string {
  const token = process.env.GITHUB_RECORDS_TOKEN;
  if (!token) throw new Error("GitHub record promotion is not configured");
  return token;
}

function repositoryApiPath(path: string): string {
  return `/repos/${RECORDS_REPOSITORY}/${path}`;
}

class GitHubClient {
  constructor(
    private readonly token: string,
    private readonly fetchImplementation: FetchImplementation,
  ) {}

  private async request(path: string, init: RequestInit = {}): Promise<Response> {
    const response = await this.fetchImplementation(`${GITHUB_API}${path}`, {
      ...init,
      cache: "no-store",
      headers: {
        Accept: "application/vnd.github+json",
        Authorization: `Bearer ${this.token}`,
        "Content-Type": "application/json",
        "User-Agent": "riemann-fail-verifier",
        "X-GitHub-Api-Version": GITHUB_API_VERSION,
        ...init.headers,
      },
    });
    if (!response.ok) {
      const detail = (await response.text()).slice(0, 500).replace(/\s+/g, " ");
      throw new GitHubPromotionError(
        `GitHub API ${response.status}: ${detail || response.statusText}`,
        response.status,
      );
    }
    return response;
  }

  async json(path: string, init: RequestInit = {}): Promise<unknown> {
    return (await this.request(path, init)).json();
  }

  async text(path: string, init: RequestInit = {}): Promise<string> {
    return (await this.request(path, init)).text();
  }
}

async function getHead(client: GitHubClient): Promise<string> {
  const response = referenceSchema.parse(
    await client.json(repositoryApiPath(`git/ref/heads/${RECORDS_BRANCH}`)),
  );
  return response.object.sha;
}

async function readRepositoryFile(
  client: GitHubClient,
  path: string,
  ref: string,
): Promise<string> {
  return client.text(
    repositoryApiPath(`contents/${path}?ref=${encodeURIComponent(ref)}`),
    { headers: { Accept: "application/vnd.github.raw+json" } },
  );
}

async function readRecords(
  client: GitHubClient,
  ref: string,
): Promise<RecordEntry[]> {
  return recordsSchema.parse(
    JSON.parse(await readRepositoryFile(client, "data/records.json", ref)),
  );
}

async function createBlob(client: GitHubClient, content: string): Promise<string> {
  return objectShaSchema.parse(
    await client.json(repositoryApiPath("git/blobs"), {
      method: "POST",
      body: JSON.stringify({ content, encoding: "utf-8" }),
    }),
  ).sha;
}

async function createTree(
  client: GitHubClient,
  baseTree: string,
  entries: Array<{ path: string; sha: string }>,
): Promise<string> {
  return objectShaSchema.parse(
    await client.json(repositoryApiPath("git/trees"), {
      method: "POST",
      body: JSON.stringify({
        base_tree: baseTree,
        tree: entries.map((entry) => ({
          ...entry,
          mode: "100644",
          type: "blob",
        })),
      }),
    }),
  ).sha;
}

async function createCommit(
  client: GitHubClient,
  message: string,
  tree: string,
  parent: string,
  date: string,
): Promise<string> {
  const identity = {
    name: "Riemann.fail Verifier",
    email: "verifier@riemann.fail",
    date,
  };
  return objectShaSchema.parse(
    await client.json(repositoryApiPath("git/commits"), {
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

function evidencePaths(submissionId: string) {
  const root = `submissions/${submissionId}`;
  return {
    root,
    manifest: `${root}/submission.json`,
    solution: `${root}/proof/Solution.lean`,
    attestation: `${root}/verification/attestation.json`,
    log: `${root}/verification/verifier.log`,
  };
}

function webBlobUrl(commit: string, path: string): string {
  return `https://github.com/${RECORDS_REPOSITORY}/blob/${commit}/${path}`;
}

function recordForSubmission(
  submission: Submission,
  attestation: VerificationAttestation,
  evidenceCommit: string,
): RecordEntry {
  const scoreDecimal = rationalToDecimal(
    submission.score.numerator,
    submission.score.denominator,
    30,
  );
  const scorePercent = rationalToDecimal(
    (BigInt(submission.score.numerator) * 100n).toString(),
    submission.score.denominator,
    28,
  );
  const paths = evidencePaths(submission.id);
  return {
    id: submission.id,
    track: submission.track,
    date: attestation.verifiedAt.slice(0, 10),
    author: submission.author.displayName,
    github: submission.author.github,
    title: `Certified critical-line bound ${scoreDecimal}`,
    method: submission.method,
    model: submission.model,
    harness: submission.harness,
    scoreDecimal,
    scorePercent,
    exactRational: submission.score,
    exactExpression: `(${submission.score.numerator} : ℝ) / ${submission.score.denominator}`,
    status: "kernel-verified",
    formalVerification: true,
    independentReview: null,
    sourceUrl: webBlobUrl(evidenceCommit, paths.manifest),
    proofUrl: webBlobUrl(evidenceCommit, paths.solution),
    pullRequestUrl: null,
    summary: submission.summary,
  };
}

function currentFormalRecord(records: RecordEntry[]): RecordEntry {
  const current = records
    .filter((record) => record.status === "kernel-verified")
    .at(-1);
  if (!current) throw new Error("No kernel-verified current record is available");
  return current;
}

function assertCurrentRecord(
  records: RecordEntry[],
  submission: Submission,
  previousRecordId: string,
): void {
  if (records.some((record) => record.id === submission.id)) {
    throw new Error(`Record already exists: ${submission.id}`);
  }
  const current = currentFormalRecord(records);
  if (current.id !== previousRecordId) {
    throw new PromotionRaceError();
  }
  if (
    current.exactRational &&
    compareRationals(submission.score, current.exactRational) <= 0
  ) {
    throw new Error("The submitted rational no longer improves the exact record");
  }
}

function parseEvidenceCommit(record: RecordEntry, submissionId: string): string {
  const paths = evidencePaths(submissionId);
  const prefix = `https://github.com/${RECORDS_REPOSITORY}/blob/`;
  const suffix = `/${paths.manifest}`;
  if (!record.sourceUrl.startsWith(prefix) || !record.sourceUrl.endsWith(suffix)) {
    throw new Error("An existing record has an unexpected evidence URL");
  }
  const commit = record.sourceUrl.slice(prefix.length, -suffix.length);
  return gitShaSchema.parse(commit);
}

async function existingPromotion(
  client: GitHubClient,
  head: string,
  submission: Submission,
  proofDigest: string,
): Promise<PromotionResult | null> {
  const records = await readRecords(client, head);
  const record = records.find((candidate) => candidate.id === submission.id);
  if (!record) return null;
  if (
    record.github?.toLowerCase() !== submission.author.github.toLowerCase() ||
    !record.exactRational ||
    compareRationals(record.exactRational, submission.score) !== 0
  ) {
    throw new Error("The submission identifier was promoted with different content");
  }

  const evidenceCommit = parseEvidenceCommit(record, submission.id);
  const paths = evidencePaths(submission.id);
  if (record.proofUrl !== webBlobUrl(evidenceCommit, paths.solution)) {
    throw new Error("An existing record has an unexpected proof URL");
  }
  const [manifest, solution] = await Promise.all([
    readRepositoryFile(client, paths.manifest, evidenceCommit),
    readRepositoryFile(client, paths.solution, evidenceCommit),
  ]);
  if (computeDirectProofDigest(manifest, solution) !== proofDigest) {
    throw new Error("The existing public evidence has a different source digest");
  }
  return {
    status: "already-promoted",
    recordId: submission.id,
    evidenceCommitSha: evidenceCommit,
    promotionCommitSha: head,
    evidenceUrl: `https://github.com/${RECORDS_REPOSITORY}/tree/${evidenceCommit}/${paths.root}`,
  };
}

async function validatePromotionInput(
  input: VerifiedPromotionInput,
  baseRecordsSnapshot: string,
): Promise<{
  submission: Submission;
  attestation: VerificationAttestation;
}> {
  gitShaSchema.parse(input.baseCommitSha);
  const submission = submissionSchema.parse(JSON.parse(input.manifest));
  const attestation = input.result.attestation;
  if (submission.id !== input.result.submissionId) {
    throw new Error("The verified result belongs to a different submission");
  }
  if (computeDirectProofDigest(input.manifest, input.solution) !== input.proofDigest) {
    throw new Error("The E2B source bundle differs from the signed upload digest");
  }
  if (input.result.proofDigest !== input.proofDigest) {
    throw new Error("The E2B result differs from the signed upload digest");
  }
  if (
    attestation.previousRecordId !== input.previousRecordId ||
    input.previousRecordId.length === 0
  ) {
    throw new Error("The attestation used a different previous record");
  }
  const verifiedAt = Date.parse(attestation.verifiedAt);
  const completedAt = Date.parse(input.result.completedAt);
  if (
    verifiedAt < input.issuedAt - 5 * 60_000 ||
    completedAt < verifiedAt ||
    completedAt > Date.now() + 5 * 60_000
  ) {
    throw new Error("The verifier timestamps are inconsistent with the signed job");
  }

  const contract = contractSchema.parse(contractJson);
  const canonicalRecordsSnapshot = `${JSON.stringify(
    recordsSchema.parse(JSON.parse(baseRecordsSnapshot)),
    null,
    2,
  )}\n`;
  const [challengeDigest, verifierTemplateDigest] = await Promise.all([
    computeTrustedMaterialDigest(process.cwd(), contract.trustedPaths, {
      "data/records.json": canonicalRecordsSnapshot,
    }),
    computeVerifierTemplateDigest(process.cwd(), contract.trustedPaths),
  ]);
  assertValidAttestation(
    submission,
    attestation,
    contract,
    challengeDigest,
    verifierTemplateDigest,
  );
  return { submission, attestation };
}

export async function promoteVerifiedSubmission(
  input: VerifiedPromotionInput,
  options: { fetchImplementation?: FetchImplementation; token?: string } = {},
): Promise<PromotionResult> {
  gitShaSchema.parse(input.baseCommitSha);
  const client = new GitHubClient(
    options.token ?? requireToken(),
    options.fetchImplementation ?? fetch,
  );

  const [initialHead, baseCommitValue, baseRecordsSnapshot] = await Promise.all([
    getHead(client),
    client.json(repositoryApiPath(`git/commits/${input.baseCommitSha}`)),
    readRepositoryFile(
      client,
      "data/records.json",
      input.baseCommitSha,
    ),
  ]);
  const baseCommit = commitSchema.parse(baseCommitValue);
  if (baseCommit.sha !== input.baseCommitSha) {
    throw new Error("GitHub returned a different base commit");
  }
  const records = recordsSchema.parse(JSON.parse(baseRecordsSnapshot));
  const { submission, attestation } = await validatePromotionInput(
    input,
    baseRecordsSnapshot,
  );

  if (initialHead !== input.baseCommitSha) {
    const existing = await existingPromotion(
      client,
      initialHead,
      submission,
      input.proofDigest,
    );
    if (existing) return existing;
    throw new PromotionRaceError();
  }

  assertCurrentRecord(records, submission, input.previousRecordId);

  const paths = evidencePaths(submission.id);
  const attestationJson = `${JSON.stringify(attestation, null, 2)}\n`;
  const log = input.result.log.endsWith("\n")
    ? input.result.log
    : `${input.result.log}\n`;
  const [manifestBlob, solutionBlob, attestationBlob, logBlob] =
    await Promise.all([
      createBlob(client, input.manifest),
      createBlob(client, input.solution),
      createBlob(client, attestationJson),
      createBlob(client, log),
    ]);
  const evidenceTree = await createTree(client, baseCommit.tree.sha, [
    { path: paths.manifest, sha: manifestBlob },
    { path: paths.solution, sha: solutionBlob },
    { path: paths.attestation, sha: attestationBlob },
    { path: paths.log, sha: logBlob },
  ]);
  const evidenceCommit = await createCommit(
    client,
    `evidence(${submission.id}): archive kernel-verified proof`,
    evidenceTree,
    input.baseCommitSha,
    attestation.verifiedAt,
  );

  const record = recordForSubmission(submission, attestation, evidenceCommit);
  records.push(record);
  recordsSchema.parse(records);
  const recordsBlob = await createBlob(
    client,
    `${JSON.stringify(records, null, 2)}\n`,
  );
  const promotionTree = await createTree(client, evidenceTree, [
    { path: "data/records.json", sha: recordsBlob },
  ]);
  const promotionCommit = await createCommit(
    client,
    `record(${submission.id}): accept ${record.scoreDecimal}`,
    promotionTree,
    evidenceCommit,
    attestation.verifiedAt,
  );

  const headBeforeUpdate = await getHead(client);
  if (headBeforeUpdate !== input.baseCommitSha) {
    const existing = await existingPromotion(
      client,
      headBeforeUpdate,
      submission,
      input.proofDigest,
    );
    if (existing) return existing;
    throw new PromotionRaceError();
  }

  try {
    const updated = referenceSchema.parse(
      await client.json(
        repositoryApiPath(`git/refs/heads/${RECORDS_BRANCH}`),
        {
          method: "PATCH",
          body: JSON.stringify({ sha: promotionCommit, force: false }),
        },
      ),
    );
    if (updated.object.sha !== promotionCommit) {
      throw new Error("GitHub returned an unexpected promoted reference");
    }
  } catch (error) {
    if (
      error instanceof GitHubPromotionError &&
      (error.status === 409 || error.status === 422)
    ) {
      const racedHead = await getHead(client);
      const existing = await existingPromotion(
        client,
        racedHead,
        submission,
        input.proofDigest,
      );
      if (existing) return existing;
      if (racedHead !== input.baseCommitSha) throw new PromotionRaceError();
    }
    throw error;
  }

  return {
    status: "promoted",
    recordId: submission.id,
    evidenceCommitSha: evidenceCommit,
    promotionCommitSha: promotionCommit,
    evidenceUrl: `https://github.com/${RECORDS_REPOSITORY}/tree/${evidenceCommit}/${paths.root}`,
  };
}

export function describePromotionError(error: unknown): string {
  if (error instanceof PromotionRaceError) {
    return `${error.message}; submit again against the new record.`;
  }
  if (error instanceof ZodError) {
    return "Verified evidence failed the trusted promotion schema.";
  }
  return error instanceof Error ? error.message : "Automatic promotion failed.";
}
