export function getE2BApiKey(): string | undefined {
  // `E2B` is retained as a temporary compatibility alias for the production
  // variable created during initial setup. New environments should use the
  // SDK-standard E2B_API_KEY name.
  return process.env.E2B_API_KEY ?? process.env.E2B;
}

export function getE2BTemplate(): string {
  return process.env.E2B_TEMPLATE_ID ?? "riemann-fail-verifier";
}

export function isE2BConfigured(): boolean {
  return Boolean(getE2BApiKey() && process.env.E2B_TEMPLATE_ID);
}
