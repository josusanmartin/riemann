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
  const hash = createHash("sha256");
  hash.update("riemann.fail/trusted-material/v1\0");
  for (const file of files) {
    if (seen.has(file.path)) {
      throw new Error(`Trusted material path is listed more than once: ${file.path}`);
    }
    seen.add(file.path);
    hash.update(file.path);
    hash.update("\0");
    hash.update(String(file.contents.byteLength));
    hash.update("\0");
    hash.update(file.contents);
    hash.update("\0");
  }
  return hash.digest("hex");
}
