import { readFile, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import { contractSchema, verificationAttestationSchema } from "../../src/lib/challenge";
import contractJson from "../../challenge/contract.json";
import { computeTrustedMaterialDigest, computeVerifierTemplateDigest } from "../../scripts/trusted-material";

const [preparedFile, exportReceipt, recordSnapshot, destination] = process.argv.slice(2);
if (!preparedFile || !exportReceipt || !recordSnapshot || !destination) {
  throw new Error("Expected prepared manifest, kernel receipt, admitted records and output path");
}
const root = resolve(import.meta.dirname, "../..");
const policy = contractSchema.parse(contractJson);
if (policy.schemaVersion !== 3) throw new Error("The compact verifier requires policy v3");
const prepared = JSON.parse(await readFile(preparedFile, "utf8"));
const evidence = JSON.parse(await readFile(exportReceipt, "utf8"));
const [challengeDigest, verifierTemplateDigest] = await Promise.all([
  computeTrustedMaterialDigest(root, policy.trustedPaths, { "data/records.json": await readFile(recordSnapshot) }),
  computeVerifierTemplateDigest(root, policy.trustedPaths),
]);
const result = verificationAttestationSchema.parse({
  ...prepared, verifiedAt: new Date().toISOString(), result: "kernel-verified", kernels: ["lean", "nanoda"],
  permittedAxioms: policy.permittedAxioms, rhFoundationCommit: policy.trustedUpstream.rh.commit,
  challengeDigest, verifierTemplateDigest, compactReplay: evidence,
});
await writeFile(destination, JSON.stringify(result, null, 2) + "\n", { flag: "wx", mode: 0o444 });
