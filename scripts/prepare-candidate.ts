import { appendFile, cp, mkdir, readFile, readdir, stat, writeFile } from "node:fs/promises";
import { basename, join, relative, resolve, sep } from "node:path";
import contractJson from "../challenge/contract.json";
import {
  contractSchema,
  compareRationals,
  rationalToDecimal,
  recordsSchema,
  submissionSchema,
} from "../src/lib/challenge";

const [submissionArgument, workspaceArgument] = process.argv.slice(2);

if (!submissionArgument || !workspaceArgument) {
  throw new Error("Usage: prepare-candidate.ts <submission-directory> <fresh-zeta23-workspace>");
}

const repositoryRoot = resolve(import.meta.dirname, "..");
const submissionDirectory = resolve(submissionArgument);
const workspace = resolve(workspaceArgument);
const contract = contractSchema.parse(contractJson);
const recordsPath = process.env.RIEMANN_RECORDS_PATH
  ? resolve(process.env.RIEMANN_RECORDS_PATH)
  : join(repositoryRoot, "data", "records.json");
const recordsJson: unknown = JSON.parse(await readFile(recordsPath, "utf8"));
const currentRecord = recordsSchema
  .parse(recordsJson)
  .filter((record) => record.status === "kernel-verified")
  .at(-1);

if (!currentRecord) {
  throw new Error("No kernel-verified current record is available");
}

function assertWithin(parent: string, child: string, label: string): void {
  const pathFromParent = relative(parent, child);
  if (pathFromParent === "" || (!pathFromParent.startsWith(`..${sep}`) && pathFromParent !== ".." && !pathFromParent.startsWith(sep))) {
    return;
  }
  throw new Error(`${label} escapes its permitted directory`);
}

async function readTemplate(name: string): Promise<string> {
  return readFile(join(repositoryRoot, "challenge", "templates", name), "utf8");
}

async function assertRegularLeanTree(
  directory: string,
  totals = { files: 0, bytes: 0 },
): Promise<void> {
  for (const entry of await readdir(directory, { withFileTypes: true })) {
    const path = join(directory, entry.name);
    if (entry.isSymbolicLink()) {
      throw new Error(`Symbolic links are not accepted in proof trees: ${path}`);
    }
    if (entry.isDirectory()) {
      await assertRegularLeanTree(path, totals);
      continue;
    }
    if (!entry.isFile() || !entry.name.endsWith(".lean")) {
      throw new Error(`Only Lean source files are accepted under proof/: ${path}`);
    }
    const fileSize = (await stat(path)).size;
    if (fileSize > 2_000_000) {
      throw new Error(`Lean source file exceeds the 2 MB limit: ${path}`);
    }
    totals.files += 1;
    totals.bytes += fileSize;
    if (totals.files > 256 || totals.bytes > 20_000_000) {
      throw new Error("A proof tree may contain at most 256 files and 20 MB of Lean source");
    }
  }
}

const submissionPath = join(submissionDirectory, "submission.json");
const submission = submissionSchema.parse(JSON.parse(await readFile(submissionPath, "utf8")));
if (
  compareRationals(submission.score, { numerator: "1", denominator: "1" }) > 0
) {
  throw new Error("A critical-line proportion cannot exceed one");
}
const proofDirectory = join(submissionDirectory, "proof");
const solutionPath = resolve(submissionDirectory, submission.proof.solution);
assertWithin(submissionDirectory, solutionPath, "proof.solution");
assertWithin(proofDirectory, solutionPath, "proof.solution");
await assertRegularLeanTree(proofDirectory);

const solution = await readFile(solutionPath, "utf8");

const candidateSpec = (await readTemplate("CandidateSpec.lean.tmpl"))
  .replace("{{CURRENT_EXPRESSION}}", currentRecord.exactExpression)
  .replace("{{NUMERATOR}}", submission.score.numerator)
  .replace("{{DENOMINATOR}}", submission.score.denominator);

await mkdir(join(workspace, "comparator", "ChallengeDeps"), { recursive: true });
await mkdir(join(workspace, "comparator", "Challenge"), { recursive: true });
await mkdir(join(workspace, "comparator", "Solution"), { recursive: true });
await mkdir(join(workspace, "comparator", "PrintAxioms"), { recursive: true });
await mkdir(join(workspace, "Candidate"), { recursive: true });

await writeFile(
  join(workspace, "comparator", "ChallengeDeps", "CandidateSpec.lean"),
  candidateSpec,
);
await writeFile(
  join(workspace, "comparator", "Challenge", "Candidate.lean"),
  await readTemplate("Challenge.Candidate.lean"),
);
await writeFile(join(workspace, "comparator", "Solution", "Candidate.lean"), solution);
await writeFile(
  join(workspace, "comparator", "PrintAxioms", "Candidate.lean"),
  await readTemplate("PrintAxioms.Candidate.lean"),
);
await appendFile(
  join(workspace, "lakefile.toml"),
  '\n[[lean_lib]]\nname = "Candidate"\n',
);

for (const entry of await readdir(proofDirectory, { withFileTypes: true })) {
  if (entry.name === basename(solutionPath)) continue;
  await cp(join(proofDirectory, entry.name), join(workspace, "Candidate", entry.name), {
    recursive: true,
    errorOnExist: true,
  });
}

const comparatorConfig = {
  challenge_module: "Challenge.Candidate",
  solution_module: "Solution.Candidate",
  theorem_names: [
    contract.theorems.strictImprovement,
    contract.theorems.dyadicBound,
    contract.theorems.cumulativeBound,
  ],
  permitted_axioms: contract.permittedAxioms,
  enable_nanoda: true,
};
await writeFile(
  join(workspace, "comparator", "config-candidate.json"),
  `${JSON.stringify(comparatorConfig, null, 2)}\n`,
);

const artifact = {
  schemaVersion: 1,
  submissionId: submission.id,
  author: submission.author,
  model: submission.model,
  harness: submission.harness,
  score: submission.score,
  scoreDecimal: rationalToDecimal(
    submission.score.numerator,
    submission.score.denominator,
    30,
  ),
  upstreamCommit: contract.trustedUpstream.commit,
  previousRecordId: currentRecord.id,
  theoremNames: comparatorConfig.theorem_names,
};
await mkdir(join(workspace, "verification-artifacts"), { recursive: true });
await writeFile(
  join(workspace, "verification-artifacts", `${submission.id}.prepared.json`),
  `${JSON.stringify(artifact, null, 2)}\n`,
);

console.log(`Prepared ${submission.id} at score ${artifact.scoreDecimal}.`);
