import { resolve } from "node:path";
import { Template } from "e2b";

export function createRiemannVerifierTemplate(
  repositoryRoot = process.cwd(),
) {
  return Template({
    // process.cwd() is the repository root both in the CLI and in the traced
    // Vercel function used for one-time production bootstrap.
    fileContextPath: resolve(repositoryRoot),
    fileIgnorePatterns: [
      ".git/**",
      ".next/**",
      ".vercel/**",
      "node_modules/**",
      "challenge/work/**",
      "verification-artifacts/**",
      ".env*",
    ],
  })
    .fromNodeImage("22")
    .aptInstall(
      [
        "bash",
        "build-essential",
        "ca-certificates",
        "coreutils",
        "curl",
        "git",
        "jq",
        "libssl-dev",
        "pkg-config",
        "python3",
        "util-linux",
        "xz-utils",
      ],
      { noInstallRecommends: true },
    )
    .runCmd("apt-get clean && rm -rf /var/lib/apt/lists/*", { user: "root" })
    .runCmd(
      "useradd --create-home --shell /bin/bash riemann && install -d -o riemann -g riemann -m 0700 /home/riemann/tmp",
      { user: "root" },
    )
    .makeDir("/opt/riemann", { user: "root", mode: 0o755 })
    .makeDir("/opt/riemann/scripts", { user: "root", mode: 0o755 })
    .copyItems([
      { src: "e2b/runtime/package.json", dest: "/opt/riemann/package.json" },
      {
        src: "e2b/runtime/package-lock.json",
        dest: "/opt/riemann/package-lock.json",
      },
      { src: "tsconfig.json", dest: "/opt/riemann/tsconfig.json" },
      { src: "challenge", dest: "/opt/riemann/challenge" },
      { src: "data", dest: "/opt/riemann/data" },
      { src: ".github", dest: "/opt/riemann/.github" },
      {
        src: "e2b/mathlib-cache-bounded-disk.patch",
        dest: "/opt/riemann/e2b/mathlib-cache-bounded-disk.patch",
      },
      {
        src: "e2b/run-verification-job.sh",
        dest: "/opt/riemann/e2b/run-verification-job.sh",
      },
      {
        src: "scripts/install-lean-toolchain.sh",
        dest: "/opt/riemann/scripts/install-lean-toolchain.sh",
      },
      {
        src: "scripts/install-native-build-toolchains.sh",
        dest: "/opt/riemann/scripts/install-native-build-toolchains.sh",
      },
      {
        src: "scripts/install-verifier-tools.sh",
        dest: "/opt/riemann/scripts/install-verifier-tools.sh",
      },
      {
        src: "scripts/lake-runtime-wrapper.sh",
        dest: "/opt/riemann/scripts/lake-runtime-wrapper.sh",
      },
      {
        src: "scripts/prepare-e2b-template.sh",
        dest: "/opt/riemann/scripts/prepare-e2b-template.sh",
      },
      {
        src: "scripts/prune-lake-build-runtime.sh",
        dest: "/opt/riemann/scripts/prune-lake-build-runtime.sh",
      },
      {
        src: "scripts/prune-lean-runtime.sh",
        dest: "/opt/riemann/scripts/prune-lean-runtime.sh",
      },
      {
        src: "scripts/run-lake-build-bounded-disk.sh",
        dest: "/opt/riemann/scripts/run-lake-build-bounded-disk.sh",
      },
      { src: "src/lib", dest: "/opt/riemann/src/lib" },
    ])
    .runCmd("chown -R riemann:riemann /opt/riemann", { user: "root" })
    .runCmd(
      [
        "cd /opt/riemann && npm ci && npm cache clean --force",
        "cd /opt/riemann && PATH=/home/riemann/.elan/bin:$PATH ./scripts/prepare-e2b-template.sh",
      ],
      { user: "riemann" },
    )
    // These files are required by the runtime attestation digest, but not by
    // the expensive formal-library build above. Keeping them in a late layer
    // lets ownership-only template corrections reuse that deterministic work.
    .copyItems([
      // Runtime-only scripts are copied after the expensive pinned formal
      // build so verifier-wrapper fixes can reuse that deterministic layer.
      { src: "scripts", dest: "/opt/riemann/scripts" },
      {
        src: "e2b/build-template.ts",
        dest: "/opt/riemann/e2b/build-template.ts",
      },
      { src: "e2b/runtime", dest: "/opt/riemann/e2b/runtime" },
      { src: "e2b/template.ts", dest: "/opt/riemann/e2b/template.ts" },
    ])
    .runCmd(
      "install -d -o root -g root -m 0755 /opt/riemann/.runtime && " +
        "cd /opt/riemann && ./node_modules/@esbuild/linux-x64/bin/esbuild " +
        "scripts/verify-submission.ts scripts/prepare-candidate.ts " +
        "scripts/finalize-e2b-job.ts --bundle --platform=node --format=esm " +
        "--outdir=/opt/riemann/.runtime --out-extension:.js=.mjs",
      { user: "root" },
    )
    .runCmd(
      [
        // Lake must inspect the pinned Git metadata after the full verifier
        // tree becomes root-owned. The Debian Git release in the Node base
        // image predates safe.directory's `dir/*` matching, so enumerate the
        // sealed dependency repositories exactly in protected system config.
        // Runtime workspaces remain owned by the unprivileged verifier user.
        "git config --system --add safe.directory /opt/riemann/zeta23",
        "find /opt/riemann/zeta23/.lake/packages -mindepth 2 -maxdepth 2 -type d -name .git -exec dirname {} + | LC_ALL=C sort | while IFS= read -r repo; do git config --system --add safe.directory \"$repo\"; done",
        "rm -rf /var/lib/apt/lists/* /home/riemann/.npm",
        "chown -R root:root /opt/riemann /home/riemann/.elan",
        "find /opt/riemann /home/riemann/.elan -type d -exec chmod a+rx,a-w {} +",
        "find /opt/riemann /home/riemann/.elan -type f -exec chmod a+r,a-w {} +",
        "chmod 0555 /opt/riemann/e2b/run-verification-job.sh /opt/riemann/scripts/*.sh /opt/riemann/tools/bin/*",
        "test -s /opt/riemann/.runtime/verify-submission.mjs && test -s /opt/riemann/.runtime/prepare-candidate.mjs && test -s /opt/riemann/.runtime/finalize-e2b-job.mjs",
        "for entry in verify-submission prepare-candidate finalize-e2b-job; do runuser -u riemann -- env -i HOME=/home/riemann PATH=/usr/local/bin:/usr/bin:/bin /usr/local/bin/node /opt/riemann/.runtime/$entry.mjs 2>&1 | grep -q 'Usage:'; done",
        "install -d -o root -g root -m 0755 /var/lib/riemann/jobs",
        "install -d -o riemann -g riemann -m 0700 /home/riemann/jobs",
      ],
      { user: "root" },
    );
}
