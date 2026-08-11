import { lstat, readFile } from "node:fs/promises";
import { resolve } from "node:path";
import {
  compareDecimalStrings,
  compareRationals,
  contractSchema,
  decimalToPercent,
  rationalToDecimal,
  recordsSchema,
} from "../src/lib/challenge";

async function readJson(path: string): Promise<unknown> {
  return JSON.parse(await readFile(resolve(path), "utf8"));
}

const contract = contractSchema.parse(await readJson("challenge/contract.json"));
const records = recordsSchema.parse(await readJson("data/records.json"));
const ids = new Set<string>();

for (const record of records) {
  if (ids.has(record.id)) {
    throw new Error(`Duplicate record id: ${record.id}`);
  }
  ids.add(record.id);
}

const baseline = records.find((record) => record.id === contract.baseline.recordId);
if (!baseline) {
  throw new Error(`Missing baseline record: ${contract.baseline.recordId}`);
}
if (baseline.scoreDecimal !== contract.baseline.decimal) {
  throw new Error("Baseline decimal differs between contract and record data");
}
if (baseline.scorePercent !== contract.baseline.percent) {
  throw new Error("Baseline percentage differs between contract and record data");
}
if (baseline.exactExpression !== contract.baseline.leanExpression) {
  throw new Error("Baseline Lean expression differs between contract and record data");
}
if (!baseline.formalVerification || baseline.status !== "kernel-verified") {
  throw new Error("Baseline must remain kernel verified");
}

const verifierInstaller = await readFile(
  resolve("scripts/install-verifier-tools.sh"),
  "utf8",
);
for (const name of Object.keys(contract.verifier)) {
  if (!verifierInstaller.includes(`contract.verifier.${name}`)) {
    throw new Error(`The verifier installer does not read contract.verifier.${name}`);
  }
}
if (!verifierInstaller.includes("contract.trustedUpstream.leanToolchain")) {
  throw new Error("The verifier installer does not read the pinned Lean toolchain");
}

for (const [sandboxEntrypoint, addressFamilyAllowList] of [
  [
    "scripts/verify-submission.ts",
    '"--property=RestrictAddressFamilies=AF_UNIX",',
  ],
  [
    "scripts/smoke-verifier.sh",
    "--property=RestrictAddressFamilies=AF_UNIX \\",
  ],
] as const) {
  const source = await readFile(resolve(sandboxEntrypoint), "utf8");
  if (!source.includes(addressFamilyAllowList)) {
    throw new Error(`${sandboxEntrypoint} must restrict sockets to the AF_UNIX allow-list`);
  }
  if (!source.includes("SystemCallArchitectures=native")) {
    throw new Error(`${sandboxEntrypoint} must prevent alternate-ABI syscall bypasses`);
  }
  if (!source.includes("SystemCallFilter=~@network-io")) {
    throw new Error(`${sandboxEntrypoint} must deny the network-I/O syscall group`);
  }
}

for (const trustedPath of contract.trustedPaths) {
  const path = resolve(trustedPath);
  const info = await lstat(path);
  if (info.isSymbolicLink()) {
    throw new Error(`Trusted path must not be a symbolic link: ${trustedPath}`);
  }
}

for (const record of records) {
  if (decimalToPercent(record.scoreDecimal) !== record.scorePercent) {
    throw new Error(`Score percentage is inconsistent for ${record.id}`);
  }
  if (record.formalVerification !== (record.status === "kernel-verified")) {
    throw new Error(`Formal-verification status is inconsistent for ${record.id}`);
  }
  if (record.formalVerification && !record.proofUrl) {
    throw new Error(`Kernel-verified record is missing a proof URL: ${record.id}`);
  }
  if (record.exactRational) {
    const exactDecimal = rationalToDecimal(
      record.exactRational.numerator,
      record.exactRational.denominator,
      30,
    );
    if (exactDecimal !== record.scoreDecimal) {
      throw new Error(`Displayed decimal is not derived from the exact rational for ${record.id}`);
    }
  }
}

for (let index = 1; index < records.length; index += 1) {
  const previous = records[index - 1];
  const current = records[index];
  const displayedComparison = compareDecimalStrings(
    current.scoreDecimal,
    previous.scoreDecimal,
  );
  if (
    displayedComparison < 0 ||
    (displayedComparison === 0 && !current.exactRational)
  ) {
    throw new Error(`Displayed record history decreases at ${current.id}`);
  }
  if (current.date < previous.date) {
    throw new Error(`Record dates move backwards at ${current.id}`);
  }
  if (
    previous.exactRational &&
    current.exactRational &&
    compareRationals(current.exactRational, previous.exactRational) <= 0
  ) {
    throw new Error(`Exact rational record history does not increase at ${current.id}`);
  }
}

console.log(`Validated ${records.length} records and challenge contract v${contract.schemaVersion}.`);
