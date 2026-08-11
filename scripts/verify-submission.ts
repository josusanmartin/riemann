import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { spawn } from "node:child_process";
import contractJson from "../challenge/contract.json";
import { contractSchema, submissionSchema } from "../src/lib/challenge";
import { computeTrustedMaterialDigest } from "./trusted-material";

type Mode = "prepare" | "quick" | "full";

const args = process.argv.slice(2);
const submissionArgument = args.find((argument) => !argument.startsWith("--"));
const modeArgument = args.find((argument) => argument.startsWith("--mode="));
const artifactArgument = args.find((argument) => argument.startsWith("--artifact="));
const mode = (modeArgument?.slice("--mode=".length) ?? "prepare") as Mode;
const artifactPath = artifactArgument
  ? resolve(artifactArgument.slice("--artifact=".length))
  : undefined;

if (!submissionArgument || !["prepare", "quick", "full"].includes(mode)) {
  throw new Error(
    "Usage: verify-submission.ts <submission-directory> [--mode=prepare|quick|full]",
  );
}

const contract = contractSchema.parse(contractJson);
const repositoryRoot = resolve(import.meta.dirname, "..");
const submissionDirectory = resolve(submissionArgument);
const prebuiltZetaWorkspace = process.env.RIEMANN_PREBUILT_ZETA23
  ? resolve(process.env.RIEMANN_PREBUILT_ZETA23)
  : undefined;
const submission = submissionSchema.parse(
  JSON.parse(await readFile(join(submissionDirectory, "submission.json"), "utf8")),
);
const workRoot = await mkdtemp(join(tmpdir(), "riemann-verifier-"));
const zetaWorkspace = join(workRoot, "zeta23");

function wait(milliseconds: number): Promise<void> {
  return new Promise((resolveWait) => setTimeout(resolveWait, milliseconds));
}

function run(
  command: string,
  commandArgs: string[],
  options: { cwd?: string; env?: NodeJS.ProcessEnv } = {},
): Promise<void> {
  return new Promise((resolveRun, rejectRun) => {
    const child = spawn(command, commandArgs, {
      cwd: options.cwd,
      env: options.env ?? process.env,
      stdio: "inherit",
    });
    child.once("error", rejectRun);
    child.once("exit", (code, signal) => {
      if (code === 0) resolveRun();
      else rejectRun(new Error(`${command} exited with ${code ?? signal}`));
    });
  });
}

async function verifyPinnedCheckout(): Promise<void> {
  const head = (
    await readFile(join(zetaWorkspace, ".git", "HEAD"), "utf8")
  ).trim();
  if (!head.startsWith("ref:") && head !== contract.trustedUpstream.commit) {
    throw new Error("Unexpected detached checkout state");
  }
  const result = await new Promise<string>((resolveResult, rejectResult) => {
    let output = "";
    const child = spawn("git", ["rev-parse", "HEAD"], {
      cwd: zetaWorkspace,
      stdio: ["ignore", "pipe", "inherit"],
    });
    child.stdout.on("data", (chunk) => {
      output += chunk.toString();
    });
    child.once("error", rejectResult);
    child.once("exit", (code) => {
      if (code === 0) resolveResult(output.trim());
      else rejectResult(new Error(`git rev-parse exited with ${code}`));
    });
  });
  if (result !== contract.trustedUpstream.commit) {
    throw new Error(`Pinned checkout mismatch: received ${result}`);
  }

  const toolchain = (await readFile(join(zetaWorkspace, "lean-toolchain"), "utf8")).trim();
  if (toolchain !== contract.trustedUpstream.leanToolchain) {
    throw new Error(`Pinned Lean toolchain mismatch: received ${toolchain}`);
  }
  const manifest = JSON.parse(
    await readFile(join(zetaWorkspace, "lake-manifest.json"), "utf8"),
  ) as { packages?: Array<{ name?: string; rev?: string }> };
  const mathlib = manifest.packages?.find((dependency) => dependency.name === "mathlib");
  if (mathlib?.rev !== contract.trustedUpstream.mathlibCommit) {
    throw new Error(`Pinned Mathlib mismatch: received ${mathlib?.rev ?? "missing"}`);
  }
}

async function cloneTrustedUpstream(): Promise<void> {
  let lastError: unknown;
  for (let attempt = 1; attempt <= 3; attempt += 1) {
    try {
      await run("git", [
        "clone",
        "--quiet",
        "--filter=blob:none",
        "--no-checkout",
        `https://github.com/${contract.trustedUpstream.repository}.git`,
        zetaWorkspace,
      ]);
      return;
    } catch (error) {
      lastError = error;
      await rm(zetaWorkspace, { recursive: true, force: true });
      if (attempt < 3) {
        console.warn(`Trusted checkout failed; retrying (${attempt + 1}/3).`);
        await wait(attempt * 5_000);
      }
    }
  }
  throw lastError;
}

async function prepareTrustedUpstream(): Promise<void> {
  if (prebuiltZetaWorkspace) {
    await mkdir(zetaWorkspace, { recursive: true });
    await run("cp", [
      "-a",
      "--no-preserve=ownership",
      "--reflink=auto",
      `${prebuiltZetaWorkspace}/.`,
      zetaWorkspace,
    ]);
    await run("chmod", ["-R", "u+w", zetaWorkspace]);
    return;
  }

  await cloneTrustedUpstream();
  await run(
    "git",
    ["checkout", "--quiet", "--detach", contract.trustedUpstream.commit],
    { cwd: zetaWorkspace },
  );
}

try {
  await prepareTrustedUpstream();
  await verifyPinnedCheckout();
  if (mode === "full" && !prebuiltZetaWorkspace) {
    console.log("Hydrating pinned Mathlib dependencies and trusted build cache.");
    await run("lake", ["exe", "cache", "get"], { cwd: zetaWorkspace });
  }
  await run(
    process.execPath,
    [
      join(repositoryRoot, "node_modules", "tsx", "dist", "cli.mjs"),
      join(repositoryRoot, "scripts", "prepare-candidate.ts"),
      submissionDirectory,
      zetaWorkspace,
    ],
    { cwd: repositoryRoot },
  );

  if (mode === "prepare") {
    console.log(`Prepared verifier workspace at ${zetaWorkspace}.`);
  } else if (mode === "quick") {
    console.warn(
      "Quick mode compiles untrusted Lean without Comparator's sandbox; use only for locally authored proofs.",
    );
    await run("lake", ["build", "Solution.Candidate"], { cwd: zetaWorkspace });
    await run(
      "lake",
      ["env", "lean", "comparator/PrintAxioms/Candidate.lean"],
      { cwd: zetaWorkspace },
    );
  } else {
    const comparator = process.env.COMPARATOR_BIN;
    if (!comparator) {
      throw new Error("COMPARATOR_BIN is required for --mode=full");
    }
    if (process.platform !== "linux") {
      throw new Error("Full Comparator verification currently requires Linux");
    }
    if (process.env.RIEMANN_OUTER_SANDBOX === "e2b") {
      await run(
        "bash",
        [
          join(repositoryRoot, "scripts", "run-comparator-e2b.sh"),
          comparator,
          "comparator/config-candidate.json",
        ],
        {
          cwd: zetaWorkspace,
          env: {
            ...process.env,
            COMPARATOR_LANDRUN: process.env.COMPARATOR_LANDRUN,
            COMPARATOR_LEAN4EXPORT: process.env.COMPARATOR_LEAN4EXPORT,
            COMPARATOR_NANODA: process.env.COMPARATOR_NANODA,
          },
        },
      );
    } else {
      await run(
        "systemd-run",
        [
        // Keep only local-domain sockets at this defense-in-depth layer;
        // @network-io below denies socket/socketpair/connect altogether.
        "--property=RestrictAddressFamilies=AF_UNIX",
        "--property=SystemCallArchitectures=native",
        "--property=SystemCallFilter=~@network-io",
        "--property=PrivateNetwork=yes",
        "--property=MemoryMax=12G",
        "--property=TasksMax=512",
        "--property=RuntimeMaxSec=9000",
        "--property=LimitFSIZE=8589934592",
        "--property=NoNewPrivileges=yes",
        "--user",
        "--pipe",
        "--wait",
        `--working-directory=${zetaWorkspace}`,
        `--setenv=PATH=${process.env.PATH ?? ""}`,
        `--setenv=COMPARATOR_LANDRUN=${process.env.COMPARATOR_LANDRUN ?? ""}`,
        `--setenv=COMPARATOR_LEAN4EXPORT=${process.env.COMPARATOR_LEAN4EXPORT ?? ""}`,
        `--setenv=COMPARATOR_NANODA=${process.env.COMPARATOR_NANODA ?? ""}`,
        "--",
        "bash",
        join(repositoryRoot, "scripts", "run-comparator-sandbox.sh"),
        comparator,
        "comparator/config-candidate.json",
        ],
        {
          cwd: zetaWorkspace,
          env: {
            ...process.env,
            COMPARATOR_LANDRUN: process.env.COMPARATOR_LANDRUN,
            COMPARATOR_LEAN4EXPORT: process.env.COMPARATOR_LEAN4EXPORT,
            COMPARATOR_NANODA: process.env.COMPARATOR_NANODA,
          },
        },
      );
    }

    if (artifactPath) {
      const prepared = JSON.parse(
        await readFile(
          join(
            zetaWorkspace,
            "verification-artifacts",
            `${submission.id}.prepared.json`,
          ),
          "utf8",
        ),
      );
      const challengeDigest = await computeTrustedMaterialDigest(
        repositoryRoot,
        contract.trustedPaths,
        process.env.RIEMANN_RECORDS_PATH
          ? {
              "data/records.json": await readFile(
                resolve(process.env.RIEMANN_RECORDS_PATH),
              ),
            }
          : undefined,
      );
      await mkdir(resolve(artifactPath, ".."), { recursive: true });
      await writeFile(
        artifactPath,
        `${JSON.stringify(
          {
            ...prepared,
            result: "kernel-verified",
            verifiedAt: new Date().toISOString(),
            challengeDigest,
            kernels: ["lean", "nanoda"],
            permittedAxioms: contract.permittedAxioms,
          },
          null,
          2,
        )}\n`,
      );
    }
  }
} finally {
  if (process.env.RIEMANN_KEEP_VERIFIER_WORK !== "1" && mode !== "prepare") {
    await rm(workRoot, { recursive: true, force: true });
  } else {
    console.log(`Preserved verifier workspace at ${workRoot}.`);
  }
}
