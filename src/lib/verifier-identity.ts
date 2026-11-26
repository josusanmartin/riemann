// Deployments supply the same source revision to health, admission and the worker.
export function deploymentVerifierCommit(): string | null {
  const platform = process.env.VERCEL_GIT_COMMIT_SHA;
  const pinned = process.env.RIEMANN_BASE_COMMIT_SHA;
  if (platform && pinned && platform !== pinned) return null;
  const sha = platform || pinned;
  return sha && /^[0-9a-f]{40}$/.test(sha) ? sha : null;
}

export function e2bTemplatePinMatches(expected: string | null) {
  return Boolean(expected && /^[0-9a-f]{64}$/.test(expected) && process.env.E2B_TEMPLATE_DIGEST === expected);
}
