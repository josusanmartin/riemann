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
      { src: "e2b", dest: "/opt/riemann/e2b" },
      { src: "scripts", dest: "/opt/riemann/scripts" },
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
        "chmod 0755 /opt/riemann/e2b/run-verification-job.sh /opt/riemann/scripts/*.sh /opt/riemann/tools/bin/*",
        "chown -R root:root /opt/riemann",
        "chmod -R a-w /opt/riemann",
        "install -d -o root -g root -m 0755 /var/lib/riemann/jobs",
        "install -d -o riemann -g riemann -m 0700 /home/riemann/jobs",
      ],
      { user: "root" },
    );
}
