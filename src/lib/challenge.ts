import { z } from "zod";

export const trackSchema = z.enum([
  "critical-line",
  "simple-critical-line",
  "distinct-zeros",
]);

export type Track = z.infer<typeof trackSchema>;

export const verificationStatusSchema = z.enum([
  "published",
  "claimed",
  "ci-passed",
  "kernel-verified",
]);

const decimalString = z
  .string()
  .regex(/^\d+\.\d+$/, "must be a non-negative decimal string");

const positiveIntegerString = z
  .string()
  .min(1)
  .max(200, "exact integers are limited to 200 digits")
  .regex(/^[1-9]\d*$/, "must be a positive integer string");

export const githubLoginSchema = z
  .string()
  .regex(/^[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?$/);

export const exactRationalSchema = z
  .object({
    numerator: positiveIntegerString,
    denominator: positiveIntegerString,
  })
  .strict();

export const independentReviewSchema = z
  .object({
    reviewer: z.string().min(1).max(120),
    date: z.string().date(),
    url: z.string().url(),
    summary: z.string().min(20).max(500),
  })
  .strict();

export const recordSchema = z
  .object({
    id: z.string().regex(/^[a-z0-9][a-z0-9-]*$/),
    track: trackSchema,
    date: z.string().date(),
    author: z.string().min(1),
    github: githubLoginSchema.nullable(),
    title: z.string().min(1),
    method: z.string().min(1),
    scoreDecimal: decimalString,
    scorePercent: decimalString,
    exactRational: exactRationalSchema.nullable(),
    exactExpression: z.string().min(1),
    status: verificationStatusSchema,
    formalVerification: z.boolean(),
    independentReview: independentReviewSchema.nullable(),
    sourceUrl: z.string().url(),
    proofUrl: z.string().url().nullable(),
    pullRequestUrl: z.string().url().nullable(),
    summary: z.string().min(1),
  })
  .strict();

export type RecordEntry = z.infer<typeof recordSchema>;

export const recordsSchema = z.array(recordSchema).min(1);

export const contractSchema = z.object({
  schemaVersion: z.literal(1),
  name: z.string().min(1),
  track: z.literal("critical-line"),
  direction: z.literal("higher"),
  trustedUpstream: z.object({
    repository: z.string().regex(/^[^/]+\/[^/]+$/),
    commit: z.string().regex(/^[0-9a-f]{40}$/),
    leanToolchain: z.string().min(1),
    mathlibCommit: z.string().regex(/^[0-9a-f]{40}$/),
  }),
  verifier: z.object({
    comparatorCommit: z.string().regex(/^[0-9a-f]{40}$/),
    landrunCommit: z.string().regex(/^[0-9a-f]{40}$/),
    lean4exportCommit: z.string().regex(/^[0-9a-f]{40}$/),
    nanodaCommit: z.string().regex(/^[0-9a-f]{40}$/),
  }),
  baseline: z.object({
    recordId: z.string().min(1),
    leanExpression: z.string().min(1),
    decimal: decimalString,
    percent: decimalString,
  }),
  theorems: z.object({
    strictImprovement: z.string().min(1),
    dyadicBound: z.string().min(1),
    cumulativeBound: z.string().min(1),
  }),
  permittedAxioms: z.array(z.string()).min(1),
  trustedPaths: z.array(z.string()).min(1),
});

export type ChallengeContract = z.infer<typeof contractSchema>;

export const submissionSchema = z
  .object({
    schemaVersion: z.literal(1),
    id: z.string().max(80).regex(/^[a-z0-9][a-z0-9-]*$/),
    track: z.literal("critical-line"),
    author: z
      .object({
        github: githubLoginSchema,
        displayName: z.string().min(1).max(100),
      })
      .strict(),
    score: exactRationalSchema,
    proof: z
      .object({
        solution: z
          .string()
          .max(240)
          .regex(/^proof\/(?:[A-Za-z][A-Za-z0-9_]*\/)*[A-Za-z][A-Za-z0-9_]*\.lean$/),
        theorem: z.literal("candidate_critical_line_bound"),
        cumulativeTheorem: z.literal("candidate_critical_line_bound_cumulative"),
        improvementTheorem: z.literal("candidate_strict_improvement"),
      })
      .strict(),
    summary: z.string().min(20).max(1000),
    method: z.string().min(3).max(200),
    license: z.literal("Apache-2.0"),
  })
  .strict();

export type Submission = z.infer<typeof submissionSchema>;

export const gitShaSchema = z.string().regex(/^[0-9a-f]{40}$/);

export const githubRepositorySchema = z
  .string()
  .max(202)
  .regex(
    /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38}[A-Za-z0-9])?\/[A-Za-z0-9_.-]+$/,
    "must be an owner/repository name",
  );

export const githubRefSchema = z
  .string()
  .min(1)
  .max(255)
  .refine(
    (value) => !/[\u0000-\u001f\u007f]/.test(value),
    "must not contain control characters",
  );

/**
 * Immutable pull-request coordinates emitted by the unprivileged verifier and
 * checked again against GitHub's API by the privileged promotion workflow.
 */
export const promotionMetadataSchema = z
  .object({
    schemaVersion: z.literal(1),
    workflowRunId: positiveIntegerString,
    pullRequestNumber: z.number().int().positive(),
    headSha: gitShaSchema,
    headRepository: githubRepositorySchema,
    headRef: githubRefSchema,
    baseSha: gitShaSchema,
    baseRepository: githubRepositorySchema,
    baseRef: githubRefSchema,
  })
  .strict();

export type PromotionMetadata = z.infer<typeof promotionMetadataSchema>;

export function compareRationals(
  left: { numerator: string; denominator: string },
  right: { numerator: string; denominator: string },
): number {
  const lhs = BigInt(left.numerator) * BigInt(right.denominator);
  const rhs = BigInt(right.numerator) * BigInt(left.denominator);
  return lhs === rhs ? 0 : lhs > rhs ? 1 : -1;
}

export function compareDecimalStrings(left: string, right: string): number {
  const [leftIntegerRaw, leftFraction = ""] = left.split(".");
  const [rightIntegerRaw, rightFraction = ""] = right.split(".");
  const leftInteger = leftIntegerRaw.replace(/^0+(?=\d)/, "");
  const rightInteger = rightIntegerRaw.replace(/^0+(?=\d)/, "");

  if (leftInteger.length !== rightInteger.length) {
    return leftInteger.length > rightInteger.length ? 1 : -1;
  }
  if (leftInteger !== rightInteger) {
    return leftInteger > rightInteger ? 1 : -1;
  }

  const width = Math.max(leftFraction.length, rightFraction.length);
  const normalizedLeft = leftFraction.padEnd(width, "0");
  const normalizedRight = rightFraction.padEnd(width, "0");
  return normalizedLeft === normalizedRight
    ? 0
    : normalizedLeft > normalizedRight
      ? 1
      : -1;
}

export function decimalToPercent(value: string): string {
  const [integer, fraction = ""] = value.split(".");
  const digits = `${integer}${fraction}`.padEnd(integer.length + 2, "0");
  const decimalPoint = integer.length + 2;
  const whole = digits.slice(0, decimalPoint).replace(/^0+(?=\d)/, "") || "0";
  const remainder = digits.slice(decimalPoint);
  return `${whole}.${remainder || "0"}`;
}

export function rationalToDecimal(
  numerator: string,
  denominator: string,
  precision = 18,
): string {
  const n = BigInt(numerator);
  const d = BigInt(denominator);
  const integer = n / d;
  let remainder = n % d;
  let fraction = "";

  for (let index = 0; index < precision; index += 1) {
    remainder *= 10n;
    fraction += (remainder / d).toString();
    remainder %= d;
  }

  return `${integer}.${fraction}`;
}
