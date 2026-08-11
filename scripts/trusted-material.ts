import { createHash } from "node:crypto";
import { lstat, readFile, readdir } from "node:fs/promises";
import { relative, resolve, sep } from "node:path";

type TrustedFile = {
  path: string;
  contents: Buffer;
};

function repositoryPath(repositoryRoot: string, path: string): string {
  const resolved = resolve(repositoryRoot, path);
  const fromRoot = relative(repositoryRoot, resolved);
  if (
    fromRoot === "" ||
    fromRoot === ".." ||
    fromRoot.startsWith(`..${sep}`) ||
    fromRoot.startsWith(sep)
  ) {
    throw new Error(`Trusted material path escapes the repository: ${path}`);
  }
  return resolved;
}

function portablePath(repositoryRoot: string, path: string): string {
  return relative(repositoryRoot, path).split(sep).join("/");
}

async function collectTrustedFiles(
  repositoryRoot: string,
  path: string,
): Promise<TrustedFile[]> {
  const info = await lstat(path);
  if (info.isSymbolicLink()) {
    throw new Error(
      `Trusted material must not contain symbolic links: ${portablePath(repositoryRoot, path)}`,
    );
  }
  if (info.isFile()) {
    return [
      {
        path: portablePath(repositoryRoot, path),
        contents: await readFile(path),
      },
    ];
  }
  if (!info.isDirectory()) {
    throw new Error(
      `Trusted material must be a regular file or directory: ${portablePath(repositoryRoot, path)}`,
    );
  }

  const entries = await readdir(path);
  const nested = await Promise.all(
    entries.sort().map((entry) =>
      collectTrustedFiles(repositoryRoot, resolve(path, entry)),
    ),
  );
  return nested.flat();
}

/**
 * Bind an attestation to every file that defines the judge, rather than only
 * the theorem templates. Paths and byte lengths are framed to avoid ambiguous
 * concatenations, and all filesystem traversal fails closed on symlinks.
 */
export async function computeTrustedMaterialDigest(
  repositoryRoot: string,
  trustedPaths: string[],
  overrides: Readonly<Record<string, string | Buffer>> = {},
): Promise<string> {
  const files = (
    await Promise.all(
      trustedPaths.map((path) =>
        collectTrustedFiles(repositoryRoot, repositoryPath(repositoryRoot, path)),
      ),
    )
  )
    .flat()
    .sort((left, right) =>
      left.path < right.path ? -1 : left.path > right.path ? 1 : 0,
    );

  const seen = new Set<string>();
  const usedOverrides = new Set<string>();
  const hash = createHash("sha256");
  hash.update("riemann.fail/trusted-material/v1\0");
  for (const file of files) {
    if (seen.has(file.path)) {
      throw new Error(`Trusted material path is listed more than once: ${file.path}`);
    }
    seen.add(file.path);
    hash.update(file.path);
    hash.update("\0");
    const override = overrides[file.path];
    const contents =
      override === undefined
        ? file.contents
        : Buffer.isBuffer(override)
          ? override
          : Buffer.from(override, "utf8");
    if (override !== undefined) usedOverrides.add(file.path);
    hash.update(String(contents.byteLength));
    hash.update("\0");
    hash.update(contents);
    hash.update("\0");
  }
  for (const path of Object.keys(overrides)) {
    if (!usedOverrides.has(path)) {
      throw new Error(`Trusted material override is not a trusted file: ${path}`);
    }
  }
  return hash.digest("hex");
}

/**
 * Hash only the immutable verifier definition baked into an E2B template.
 * The record ledger is uploaded per job and is bound separately to the signed
 * base commit, so it must not make an otherwise-current template look stale.
 */
export function verifierTemplateTrustedPaths(
  trustedPaths: string[],
): string[] {
  const paths = trustedPaths.filter((path) => path !== "data/records.json");
  if (paths.length === trustedPaths.length) {
    throw new Error("Trusted paths must include data/records.json");
  }
  return paths;
}

export function computeVerifierTemplateDigest(
  repositoryRoot: string,
  trustedPaths: string[],
): Promise<string> {
  return computeTrustedMaterialDigest(
    repositoryRoot,
    verifierTemplateTrustedPaths(trustedPaths),
  );
}
