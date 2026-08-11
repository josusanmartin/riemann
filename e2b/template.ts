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
        "cargo",
        "coreutils",
        "curl",
        "git",
        "golang-go",
        "jq",
        "libssl-dev",
        "pkg-config",
        "python3",
        "util-linux",
        "xz-utils",
      ],
      { noInstallRecommends: true },
    )
    .runCmd(
      "useradd --create-home --shell /bin/bash riemann && install -d -o riemann -g riemann -m 0700 /home/riemann/tmp",
      { user: "root" },
    )
    .makeDir("/opt/riemann", { user: "root", mode: 0o755 })
    .copyItems([
      { src: "package.json", dest: "/opt/riemann/package.json" },
      { src: "package-lock.json", dest: "/opt/riemann/package-lock.json" },
      { src: "tsconfig.json", dest: "/opt/riemann/tsconfig.json" },
      { src: "challenge", dest: "/opt/riemann/challenge" },
      { src: "data", dest: "/opt/riemann/data" },
      { src: ".github", dest: "/opt/riemann/.github" },
      { src: "e2b", dest: "/opt/riemann/e2b" },
      { src: "scripts", dest: "/opt/riemann/scripts" },
      { src: "src/lib", dest: "/opt/riemann/src/lib" },
    ])
    .runCmd(
      [
        "chown -R riemann:riemann /opt/riemann",
        "cd /opt/riemann && npm ci",
        "cd /opt/riemann && PATH=/home/riemann/.elan/bin:$PATH ./scripts/prepare-e2b-template.sh",
      ],
      { user: "riemann" },
    )
    .runCmd(
      [
        "chmod 0755 /opt/riemann/e2b/run-verification-job.sh /opt/riemann/scripts/*.sh",
        "chown -R root:root /opt/riemann",
        "chmod -R a-w /opt/riemann",
        "install -d -o root -g root -m 0755 /var/lib/riemann/jobs",
        "install -d -o riemann -g riemann -m 0700 /home/riemann/jobs",
      ],
      { user: "root" },
    );
}
