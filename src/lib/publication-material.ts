import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { z } from "zod";
import contract from "../../challenge/contract.json";
import { computeTrustedMaterialDigest, computeVerifierTemplateDigest } from "../../scripts/trusted-material";
import { deploymentVerifierCommit } from "./verifier-identity";

const ledgerPath = "data/records.json";
const bundleSchema = z.object({
  revision: z.string().regex(/^[0-9a-f]{40}$/),
  before: z.string(),
  after: z.string(),
  records: z.string(),
}).strict();

export class PublicationMaterialUnavailable extends Error {}

export function readReleaseMaterial(bytes: Buffer, revision: string | null, pin: string | undefined) {
  if (!revision || createHash("sha256").update(bytes).digest("hex") !== pin) {
    throw new Error("Publication material does not match its release pin");
  }
  const bundle = bundleSchema.parse(JSON.parse(bytes.toString("utf8")));
  if (bundle.revision !== revision) throw new Error("Publication material belongs to another deployment");
  const before = Buffer.from(bundle.before, "base64");
  const after = Buffer.from(bundle.after, "base64");
  const records = Buffer.from(bundle.records, "base64");
  const prefix = createHash("sha256").update(before);
  const template = prefix.copy().update(after).digest("hex");
  return (snapshot?: string) => {
    const content = snapshot === undefined ? records : Buffer.from(snapshot, "utf8");
    const challenge = prefix.copy().update(ledgerPath).update("\0").update(String(content.length))
      .update("\0").update(content).update("\0").update(after).digest("hex");
    return { template, challenge };
  };
}

let loaded: { revision: string; pin: string; digests: ReturnType<typeof readReleaseMaterial> } | undefined;

export async function publicationDigests(snapshot?: string) {
  if (process.env.VERCEL_ENV === "production" || process.env.RIEMANN_PUBLICATION_MATERIAL_SHA256) {
    try {
      const revision = deploymentVerifierCommit();
      const pin = process.env.RIEMANN_PUBLICATION_MATERIAL_SHA256;
      if (!revision || !pin) throw new Error("Missing release pin");
      if (loaded?.revision !== revision || loaded.pin !== pin) {
        const bytes = await readFile(resolve(process.cwd(), "publication-material.bin"));
        loaded = { revision, pin, digests: readReleaseMaterial(bytes, revision, pin) };
      }
      return loaded.digests(snapshot);
    } catch {
      throw new PublicationMaterialUnavailable("The publisher could not load the verifier material pinned to its deployment");
    }
  }
  const [template, challenge] = await Promise.all([
    computeVerifierTemplateDigest(process.cwd(), contract.trustedPaths),
    computeTrustedMaterialDigest(process.cwd(), contract.trustedPaths, snapshot === undefined ? {} : { [ledgerPath]: snapshot }),
  ]);
  return { template, challenge };
}

export async function publicationReady() {
  try {
    await publicationDigests();
    return true;
  } catch {
    return false;
  }
}
