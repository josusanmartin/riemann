import { z } from "zod";

export const verifierFeedbackSchema = z
  .object({
    code: z.enum([
      "submission-invalid",
      "lean-parse-failed",
      "lean-elaboration-failed",
      "required-theorem-missing",
      "theorem-contract-mismatch",
      "unpermitted-axiom",
      "nanoda-rejected",
      "lean-kernel-rejected",
      "verification-timeout",
      "sandbox-expired",
      "verifier-infrastructure",
      "unclassified-rejection",
    ]),
    stage: z.enum([
      "submission",
      "lean-compilation",
      "theorem-contract",
      "axiom-audit",
      "nanoda-kernel",
      "lean-kernel",
      "runtime",
      "infrastructure",
      "unknown",
    ]),
    title: z.string().min(1).max(120),
    detail: z.string().min(1).max(600),
    action: z.string().min(1).max(600),
    retryable: z.boolean(),
    location: z
      .object({
        file: z.literal("Solution.lean"),
        line: z.number().int().positive().max(10_000_000),
        column: z.number().int().nonnegative().max(1_000_000),
      })
      .strict()
      .optional(),
  })
  .strict();

export type VerifierFeedback = z.infer<typeof verifierFeedbackSchema>;

function feedback(value: VerifierFeedback): VerifierFeedback {
  return verifierFeedbackSchema.parse(value);
}

function candidateLocation(log: string): VerifierFeedback["location"] {
  const match = log.match(
    /(?:^|[\\/\s])Solution(?:[\\/]Candidate)?\.lean:(\d+):(\d+)(?::|\b)/im,
  );
  if (!match) return undefined;
  const line = Number(match[1]);
  const column = Number(match[2]);
  if (
    !Number.isSafeInteger(line) ||
    line <= 0 ||
    line > 10_000_000 ||
    !Number.isSafeInteger(column) ||
    column < 0 ||
    column > 1_000_000
  ) {
    return undefined;
  }
  return { file: "Solution.lean", line, column };
}

/**
 * Turn an untrusted verifier log into a fixed, safe diagnosis.
 *
 * Queue receipts are public, so this function must never copy source text,
 * paths, identifiers, or arbitrary log excerpts into its return value.
 */
export function describeVerifierRejection(
  log: string,
  fallbackMessage: string,
): VerifierFeedback {
  const diagnostic = `${fallbackMessage}\n${log}`.toLowerCase();
  const location = candidateLocation(log);

  if (
    diagnostic.includes("expired before producing a result") ||
    diagnostic.includes("sandbox expired before") ||
    diagnostic.includes("sandbox was not found")
  ) {
    return feedback({
      code: "sandbox-expired",
      stage: "infrastructure",
      title: "Verification sandbox expired",
      detail:
        "The isolated checker disappeared before it could save a mathematical verdict. This is an infrastructure failure, not evidence that the proof is wrong.",
      action:
        "Submit the same source again. If it happens repeatedly, send the proof digest to the maintainers so they can trace the sandbox lifecycle.",
      retryable: true,
    });
  }

  if (
    diagnostic.includes("exceeded the verifier runtime limit") ||
    diagnostic.includes("exceeded its runtime limit") ||
    diagnostic.includes("verification timed out") ||
    diagnostic.includes("exited with status 124") ||
    diagnostic.includes("exited with status 137")
  ) {
    return feedback({
      code: "verification-timeout",
      stage: "runtime",
      title: "Verification timed out",
      detail:
        "The checker reached its runtime limit before Lean and both kernels completed. No accepted mathematical verdict was produced.",
      action:
        "Reduce elaboration cost, replace expensive tactics with smaller explicit lemmas, and test the source locally before submitting again.",
      retryable: false,
    });
  }

  if (
    diagnostic.includes("only lean source files are accepted") ||
    diagnostic.includes("symbolic links are not accepted") ||
    diagnostic.includes("lean source file exceeds") ||
    diagnostic.includes("proof tree may contain at most") ||
    diagnostic.includes("escapes its permitted directory") ||
    diagnostic.includes("critical-line proportion cannot exceed one") ||
    diagnostic.includes("usage: verify-submission")
  ) {
    return feedback({
      code: "submission-invalid",
      stage: "submission",
      title: "Submission format was rejected",
      detail:
        "The upload did not satisfy the checker’s source, size, path, or score constraints, so formal verification did not start.",
      action:
        "Submit one plain Solution.lean file within the size limit, keep the score at most 1, and use the required record fields shown in the form.",
      retryable: false,
    });
  }

  if (
    diagnostic.includes("const not found in solution") ||
    diagnostic.includes("constant not found in solution") ||
    diagnostic.includes("solution constant is not a theorem") ||
    diagnostic.includes("solution constant is not a definition")
  ) {
    return feedback({
      code: "required-theorem-missing",
      stage: "theorem-contract",
      title: "A required theorem is missing",
      detail:
        "The source compiled far enough to inspect its exports, but it did not provide every locked theorem declaration with the required kind.",
      action:
        "Start from the challenge template and export all three required theorem names without renaming them or replacing a theorem with a definition or axiom.",
      retryable: false,
    });
  }

  if (
    diagnostic.includes("theorem statement do not match") ||
    diagnostic.includes("constant kind don't match") ||
    diagnostic.includes("const does not match between challenge and target") ||
    diagnostic.includes("challenge constant is not a definition")
  ) {
    return feedback({
      code: "theorem-contract-mismatch",
      stage: "theorem-contract",
      title: "The theorem contract does not match",
      detail:
        "A required declaration was found, but its exact type or a locked dependency differs from the challenge statement.",
      action:
        "Copy the theorem signatures from the current template exactly and change only the proof bodies and permitted helper lemmas.",
      retryable: false,
    });
  }

  if (diagnostic.includes("illegal axiom detected")) {
    return feedback({
      code: "unpermitted-axiom",
      stage: "axiom-audit",
      title: "The proof uses an unpermitted axiom",
      detail:
        "The exported proof depends on an axiom outside the challenge allowlist: propext, Quot.sound, and Classical.choice.",
      action:
        "Remove sorry, custom axioms, and unsafe shortcuts, then rebuild and inspect the theorem’s axioms before resubmitting.",
      retryable: false,
    });
  }

  if (
    diagnostic.includes("nanoda kernel rejected the solution")
  ) {
    return feedback({
      code: "nanoda-rejected",
      stage: "nanoda-kernel",
      title: "Nanoda rejected the exported proof",
      detail:
        "Lean produced an export, but the independent nanoda kernel could not replay and accept it.",
      action:
        "Check for unsupported or unpermitted dependencies in the proof. If Lean accepts it locally and nanoda still fails, share the digest and private log with the maintainers.",
      retryable: false,
    });
  }

  if (diagnostic.includes("lean default kernel rejects the solution")) {
    return feedback({
      code: "lean-kernel-rejected",
      stage: "lean-kernel",
      title: "Lean kernel replay rejected the proof",
      detail:
        "The exported environment could not be replayed by Lean’s default kernel, so the checker could not certify the proof.",
      action:
        "Inspect the technical log for the first kernel error. Remove malformed or unsupported declarations, rebuild locally, and submit again.",
      retryable: false,
    });
  }

  if (
    diagnostic.includes("unexpected token") ||
    diagnostic.includes("unexpected identifier") ||
    diagnostic.includes("unexpected end of input") ||
    diagnostic.includes("unterminated") ||
    diagnostic.includes("invalid syntax") ||
    diagnostic.includes("parser error")
  ) {
    return feedback({
      code: "lean-parse-failed",
      stage: "lean-compilation",
      title: "Lean could not parse the source",
      detail:
        "The submitted Lean file contains a syntax error, so the checker could not compile the candidate module.",
      action:
        "Open the technical log, fix the first parser error and its line and column, then run the local verifier before resubmitting.",
      retryable: false,
      ...(location ? { location } : {}),
    });
  }

  if (
    diagnostic.includes("unknown identifier") ||
    diagnostic.includes("unknown constant") ||
    diagnostic.includes("unknown module prefix") ||
    diagnostic.includes("failed to synthesize") ||
    diagnostic.includes("type mismatch") ||
    diagnostic.includes("unsolved goals") ||
    diagnostic.includes("declaration has metavariables") ||
    diagnostic.includes("invalid field") ||
    diagnostic.includes("no goals to be solved") ||
    diagnostic.includes("function expected") ||
    diagnostic.includes("tactic execution") ||
    diagnostic.includes("tactic '") ||
    diagnostic.includes("tactic failed")
  ) {
    return feedback({
      code: "lean-elaboration-failed",
      stage: "lean-compilation",
      title: "Lean could not elaborate the proof",
      detail:
        "The source parsed, but Lean found an unresolved name, type mismatch, missing instance, failed tactic, metavariable, or unfinished goal.",
      action:
        "Open the technical log and fix the first Lean error; later errors are often consequences of that one. Rebuild locally before resubmitting.",
      retryable: false,
      ...(location ? { location } : {}),
    });
  }

  if (
    diagnostic.includes("refusing to run") ||
    diagnostic.includes("unexpected detached checkout state") ||
    diagnostic.includes("pinned checkout mismatch") ||
    diagnostic.includes("prebuilt trusted zeta23 runtime is incomplete") ||
    diagnostic.includes("no kernel-verified current record is available") ||
    diagnostic.includes("eacces") ||
    diagnostic.includes("enoent") ||
    diagnostic.includes("out of memory") ||
    diagnostic.includes("cannot allocate memory") ||
    diagnostic.includes("segmentation fault") ||
    diagnostic.includes("error while interacting with nanoda") ||
    (diagnostic.includes("building challenge.candidate") &&
      !diagnostic.includes("building solution.candidate"))
  ) {
    return feedback({
      code: "verifier-infrastructure",
      stage: "infrastructure",
      title: "Verifier infrastructure failed",
      detail:
        "The trusted checker environment failed before it could produce a mathematical verdict. This does not show that the submitted proof is wrong.",
      action:
        "Retry later. If the same digest fails again, send the digest to the maintainers so they can inspect the private operational logs.",
      retryable: true,
    });
  }

  if (
    diagnostic.includes("building solution.candidate") &&
    (diagnostic.includes("child exited with") ||
      diagnostic.includes("lake exited with"))
  ) {
    return feedback({
      code: "lean-elaboration-failed",
      stage: "lean-compilation",
      title: "Lean could not compile the candidate",
      detail:
        "The candidate module failed during Lean compilation before theorem comparison or kernel replay could complete.",
      action:
        "Open the technical log and resolve the first compiler error, then run the local verifier before submitting again.",
      retryable: false,
      ...(location ? { location } : {}),
    });
  }

  return feedback({
    code: "unclassified-rejection",
    stage: "unknown",
    title: "The checker could not accept the proof",
    detail:
      "The verifier exited without a recognized diagnosis. The proof was not certified, but the summary alone cannot identify the mathematical cause.",
    action:
      "Open the technical verifier log and start with its first error. If it is unclear, send the proof digest and private log to the maintainers.",
    retryable: false,
  });
}
