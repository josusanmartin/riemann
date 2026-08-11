import { createHash } from "node:crypto";
import { describe, expect, it } from "vitest";
import {
  contract,
  getCurrentRecord,
  records,
} from "@/lib/records";
import { prepareDirectSubmission } from "@/lib/direct-submission";
import { rationalToDecimal, type VerificationAttestation } from "@/lib/challenge";
import type { E2BVerificationResult } from "@/lib/e2b-verifier";
import {
  promoteVerifiedSubmission,
  PromotionRaceError,
} from "@/lib/github-promotion";
import {
  computeTrustedMaterialDigest,
  computeVerifierTemplateDigest,
} from "../../scripts/trusted-material";

type RequestLog = { url: URL; method: string; body?: unknown };

function sha(value: string): string {
  return createHash("sha1").update(value).digest("hex");
}

const canonicalRecordsSnapshot = `${JSON.stringify(records, null, 2)}\n`;

function fakeGitHub(
  initialHead: string,
  baseRecordsSnapshot = canonicalRecordsSnapshot,
) {
  let head = initialHead;
  const requests: RequestLog[] = [];
  const blobs = new Map<string, string>();
  let sequence = 0;

  const fetchImplementation: typeof fetch = async (input, init = {}) => {
    const url = new URL(typeof input === "string" ? input : input.toString());
    const method = init.method ?? "GET";
    const body = typeof init.body === "string" ? JSON.parse(init.body) : undefined;
    requests.push({ url, method, body });

    const response = (value: unknown, status = 200) =>
      new Response(typeof value === "string" ? value : JSON.stringify(value), {
        status,
        headers: { "Content-Type": "application/json" },
      });
    if (url.pathname.endsWith("/git/ref/heads/main") && method === "GET") {
      return response({ object: { sha: head } });
    }
    if (url.pathname.includes("/git/commits/") && method === "GET") {
      return response({
        sha: url.pathname.split("/").at(-1),
        tree: { sha: sha("base-tree") },
      });
    }
    if (url.pathname.endsWith("/contents/data/records.json")) {
      return response(baseRecordsSnapshot);
    }
    if (url.pathname.endsWith("/git/blobs") && method === "POST") {
      const content = String((body as { content: string }).content);
      const blobSha = sha(`blob ${content.length}\0${content}`);
      blobs.set(blobSha, content);
      return response({ sha: blobSha }, 201);
    }
    if (url.pathname.endsWith("/git/trees") && method === "POST") {
      sequence += 1;
      return response({ sha: sha(`tree-${sequence}-${JSON.stringify(body)}`) }, 201);
    }
    if (url.pathname.endsWith("/git/commits") && method === "POST") {
      sequence += 1;
      return response({ sha: sha(`commit-${sequence}-${JSON.stringify(body)}`) }, 201);
    }
    if (url.pathname.endsWith("/git/refs/heads/main") && method === "PATCH") {
      head = String((body as { sha: string }).sha);
      return response({ object: { sha: head } });
    }
    return response({ message: `Unhandled ${method} ${url.pathname}` }, 500);
  };
  return { fetchImplementation, requests, blobs, getHead: () => head };
}

async function fixture(recordsSnapshot = canonicalRecordsSnapshot) {
  const prepared = prepareDirectSubmission(
    {
      id: "direct-record-test",
      displayName: "Direct Solver",
      score: { numerator: "672500704", denominator: "1000000000" },
      summary: "A complete direct candidate used to test atomic publication.",
      method: "A formally checked refinement",
      solution: "import ChallengeDeps\n-- complete declarations\n",
      acceptLicense: true,
    },
    "direct-solver",
    getCurrentRecord(),
  );
  const verifiedAt = new Date().toISOString();
  const attestation: VerificationAttestation = {
    schemaVersion: 1,
    submissionId: prepared.submission.id,
    author: prepared.submission.author,
    score: prepared.submission.score,
    scoreDecimal: rationalToDecimal("672500704", "1000000000", 30),
    previousRecordId: getCurrentRecord().id,
    upstreamCommit: contract.trustedUpstream.commit,
    theoremNames: [
      contract.theorems.strictImprovement,
      contract.theorems.dyadicBound,
      contract.theorems.cumulativeBound,
    ],
    result: "kernel-verified",
    verifiedAt,
    challengeDigest: await computeTrustedMaterialDigest(
      process.cwd(),
      contract.trustedPaths,
      { "data/records.json": recordsSnapshot },
    ),
    verifierTemplateDigest: await computeVerifierTemplateDigest(
      process.cwd(),
      contract.trustedPaths,
    ),
    kernels: ["lean", "nanoda"],
    permittedAxioms: contract.permittedAxioms,
  };
  const result: Extract<E2BVerificationResult, { status: "verified" }> = {
    schemaVersion: 1,
    status: "verified",
    submissionId: prepared.submission.id,
    proofDigest: prepared.proofDigest,
    completedAt: verifiedAt,
    log: "Comparator and both kernels accepted.\n",
    attestation,
  };
  return { prepared, result, verifiedAt };
}

describe("automatic GitHub record promotion", () => {
  it("publishes evidence and the ledger through one non-forced ref update", async () => {
    const baseCommitSha = "a".repeat(40);
    const github = fakeGitHub(baseCommitSha);
    const { prepared, result } = await fixture();
    const promotion = await promoteVerifiedSubmission(
      {
        baseCommitSha,
        previousRecordId: getCurrentRecord().id,
        proofDigest: prepared.proofDigest,
        issuedAt: Date.now() - 1_000,
        manifest: prepared.manifest,
        solution: prepared.solution,
        result,
      },
      { token: "test-token", fetchImplementation: github.fetchImplementation },
    );

    expect(promotion.status).toBe("promoted");
    const commits = github.requests.filter(
      (request) => request.method === "POST" && request.url.pathname.endsWith("/git/commits"),
    );
    expect(commits).toHaveLength(2);
    expect((commits[0].body as { parents: string[] }).parents).toEqual([
      baseCommitSha,
    ]);
    expect((commits[1].body as { parents: string[] }).parents).toEqual([
      promotion.evidenceCommitSha,
    ]);
    const refUpdate = github.requests.find(
      (request) => request.method === "PATCH" && request.url.pathname.endsWith("/git/refs/heads/main"),
    );
    expect(refUpdate?.body).toMatchObject({
      sha: promotion.promotionCommitSha,
      force: false,
    });
    expect(github.getHead()).toBe(promotion.promotionCommitSha);

    const recordsBlob = [...github.blobs.values()].find((content) => {
      try {
        const parsed = JSON.parse(content) as unknown;
        return Array.isArray(parsed) && parsed.at(-1)?.id === prepared.submission.id;
      } catch {
        return false;
      }
    });
    const promoted = JSON.parse(recordsBlob ?? "[]").at(-1);
    expect(promoted.sourceUrl).toContain(promotion.evidenceCommitSha);
    expect(promoted.pullRequestUrl).toBeNull();
  });

  it("fails closed when main no longer matches the verified deployment", async () => {
    const { prepared, result } = await fixture();
    const github = fakeGitHub("b".repeat(40));
    await expect(
      promoteVerifiedSubmission(
        {
          baseCommitSha: "a".repeat(40),
          previousRecordId: getCurrentRecord().id,
          proofDigest: prepared.proofDigest,
          issuedAt: Date.now() - 1_000,
          manifest: prepared.manifest,
          solution: prepared.solution,
          result,
        },
        { token: "test-token", fetchImplementation: github.fetchImplementation },
      ),
    ).rejects.toBeInstanceOf(PromotionRaceError);
    expect(github.requests.some((request) => request.method === "POST")).toBe(false);
  });

  it("checks the attestation against the exact ledger bytes at the base commit", async () => {
    const baseCommitSha = "c".repeat(40);
    const baseRecordsSnapshot = JSON.stringify(records);
    const github = fakeGitHub(baseCommitSha, baseRecordsSnapshot);
    const { prepared, result } = await fixture();

    await expect(
      promoteVerifiedSubmission(
        {
          baseCommitSha,
          previousRecordId: getCurrentRecord().id,
          proofDigest: prepared.proofDigest,
          issuedAt: Date.now() - 1_000,
          manifest: prepared.manifest,
          solution: prepared.solution,
          result,
        },
        { token: "test-token", fetchImplementation: github.fetchImplementation },
      ),
    ).resolves.toMatchObject({ status: "promoted" });
  });

  it("rejects an attestation produced by a stale verifier template", async () => {
    const baseCommitSha = "d".repeat(40);
    const github = fakeGitHub(baseCommitSha);
    const { prepared, result } = await fixture();
    const staleResult = {
      ...result,
      attestation: {
        ...result.attestation,
        verifierTemplateDigest: "0".repeat(64),
      },
    };

    await expect(
      promoteVerifiedSubmission(
        {
          baseCommitSha,
          previousRecordId: getCurrentRecord().id,
          proofDigest: prepared.proofDigest,
          issuedAt: Date.now() - 1_000,
          manifest: prepared.manifest,
          solution: prepared.solution,
          result: staleResult,
        },
        { token: "test-token", fetchImplementation: github.fetchImplementation },
      ),
    ).rejects.toThrow("Verifier template is stale");
    expect(github.requests.some((request) => request.method === "POST")).toBe(false);
  });
});
