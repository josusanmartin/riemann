import type { NextConfig } from "next";

const securityHeaders = [
  { key: "Cross-Origin-Opener-Policy", value: "same-origin" },
  { key: "Cross-Origin-Resource-Policy", value: "same-origin" },
  { key: "Origin-Agent-Cluster", value: "?1" },
  { key: "X-DNS-Prefetch-Control", value: "off" },
  { key: "X-Content-Type-Options", value: "nosniff" },
  { key: "X-Frame-Options", value: "DENY" },
  { key: "X-Permitted-Cross-Domain-Policies", value: "none" },
  { key: "Referrer-Policy", value: "strict-origin-when-cross-origin" },
  {
    key: "Permissions-Policy",
    value: "camera=(), microphone=(), geolocation=(), browsing-topics=()",
  },
  {
    key: "Strict-Transport-Security",
    value: "max-age=63072000; includeSubDomains; preload",
  },
];

const trustedPromotionRuntimeFiles = [
  ".github/workflows/build-e2b-template.yml",
  ".github/workflows/verifier-smoke.yml",
  "challenge/**/*",
  "data/**/*",
  "e2b/**/*",
  "package.json",
  "package-lock.json",
  "scripts/**/*",
  "src/lib/**/*",
];

const verifierTemplateBuildFiles = [
  ...trustedPromotionRuntimeFiles,
  ".github/**/*",
  "node_modules/glob/**/*",
  "tsconfig.json",
];

const nextConfig: NextConfig = {
  poweredByHeader: false,
  turbopack: { root: process.cwd() },
  outputFileTracingIncludes: {
    "/api/submissions/status": trustedPromotionRuntimeFiles,
    "/api/e2b/webhook": trustedPromotionRuntimeFiles,
    "/api/e2b/sweep": trustedPromotionRuntimeFiles,
    "/api/health": trustedPromotionRuntimeFiles,
    "/api/admin/e2b-template": verifierTemplateBuildFiles,
  },
  async headers() {
    return [{ source: "/(.*)", headers: securityHeaders }];
  },
};

export default nextConfig;
