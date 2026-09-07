import type { Sandbox } from "e2b";
import { contract } from "./records";
import { computeVerifierTemplateDigest, verifierTemplateTrustedPaths } from "../../scripts/trusted-material";

export class VerifierTemplateMismatchError extends Error {
  constructor() {
    super("The verifier image does not match this deployment. Maintainers must rebuild and pin the image; no daily submission slot was consumed.");
    this.name = "VerifierTemplateMismatchError";
  }
}

// Standard Node only: runnable even in an older sealed image. No candidate
// source is uploaded before this read-only root-side identity check.
export function verifierDigestCommand(root = "/opt/riemann"): string {
  const source = `
import { createHash } from 'node:crypto';
import { lstat, readdir, readFile } from 'node:fs/promises';
import { resolve, relative } from 'node:path';
const root = ${JSON.stringify(root)};
const files = [];
async function visit(path) {
  const full = resolve(root, path);
  const info = await lstat(full);
  if (info.isSymbolicLink()) throw Error('Unsealed trusted symlink');
  if (info.isFile()) files.push(relative(root, full));
  else if (info.isDirectory()) for (const entry of await readdir(full)) await visit(path + '/' + entry);
  else throw Error('Unexpected trusted file type');
}
for (const path of ${JSON.stringify(verifierTemplateTrustedPaths(contract.trustedPaths))}) await visit(path);
files.sort();
if (new Set(files).size !== files.length) throw Error('Duplicate trusted file');
const hash = createHash('sha256').update('riemann.fail/trusted-material/v1\\0');
for (const path of files) {
  const contents = await readFile(resolve(root, path));
  hash.update(path).update('\\0').update(String(contents.length)).update('\\0').update(contents).update('\\0');
}
console.log(hash.digest('hex'));
`;
  return `node --input-type=module -e '${source.replaceAll("'", "'\\''")}'`;
}

export async function inspectVerifierReadiness(sandbox: Pick<Sandbox, "commands">) {
  const [expected, actual] = await Promise.all([
    computeVerifierTemplateDigest(process.cwd(), contract.trustedPaths),
    sandbox.commands.run(verifierDigestCommand(), { user: "root", timeoutMs: 15_000 }),
  ]);
  const received = actual.stdout.trim();
  if (!/^[0-9a-f]{64}$/.test(received)) throw new Error("Invalid verifier identity response");
  return { expected, actual: received, matches: expected === received };
}

export async function assertVerifierReady(sandbox: Pick<Sandbox, "commands">) {
  const readiness = await inspectVerifierReadiness(sandbox);
  if (!readiness.matches) throw new VerifierTemplateMismatchError();
}
