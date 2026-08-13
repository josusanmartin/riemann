import { z } from "zod";
import { prepareDirectSubmission } from "@/lib/direct-submission";
import {
  FLOW_TEST_SCORE,
  flowTestRecord,
} from "@/lib/flow-test";

const flowTestInputSchema = z
  .object({ solution: z.string().min(1).max(2_000_000) })
  .strict();

export function prepareFlowTestSubmission(
  rawInput: unknown,
  github: string,
  displayName: string,
  issuedAt = Date.now(),
) {
  const { solution } = flowTestInputSchema.parse(rawInput);
  return prepareDirectSubmission(
    {
      id: `flow-test-${issuedAt}`,
      displayName: displayName.trim().slice(0, 100) || github,
      score: FLOW_TEST_SCORE,
      summary:
        "Noncompetitive end-to-end replay of Anthropic's unconditional two-thirds theorem.",
      method: "Anthropic Zeta23 theorem replay",
      model: "Claude / Anthropic",
      harness: "Riemann.fail official flow test",
      solution,
      acceptLicense: true,
    },
    github,
    flowTestRecord,
  );
}
