import { describe, expect, it } from "vitest";
import {
  signSubmissionJob,
  verifySubmissionJob,
  type SubmissionJobToken,
} from "@/lib/submission-jobs";

const payload: SubmissionJobToken = {
  schemaVersion: 1,
  sandboxId: "sandbox-1234567890",
  jobId: "4d664a5f-65f8-40c9-a641-6bb9eb77ef6b",
  submissionId: "direct-proof",
  github: "actual-solver",
  proofDigest: "a".repeat(64),
  baseCommitSha: "b".repeat(40),
  previousRecordId: "current-record",
  issuedAt: 1_000,
  expiresAt: 10_000,
};

describe("submission job tokens", () => {
  it("round-trips an authenticated opaque job handle", () => {
    const token = signSubmissionJob(payload, "test-secret");
    expect(verifySubmissionJob(token, "test-secret", 5_000)).toEqual(payload);
  });

  it("rejects tampering and expiry", () => {
    const token = signSubmissionJob(payload, "test-secret");
    expect(() => verifySubmissionJob(`${token}x`, "test-secret", 5_000)).toThrow();
    expect(() => verifySubmissionJob(token, "test-secret", 10_000)).toThrow(
      "expired",
    );
  });
});
