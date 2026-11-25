export function contentPolicy(nonce?: string) {
  const development = process.env.NODE_ENV === "development";
  const scripts = nonce ? `'nonce-${nonce}' 'strict-dynamic' 'self'` : "'self' 'unsafe-inline'";
  return [
    "default-src 'self'", "object-src 'none'", "base-uri 'none'", "frame-ancestors 'none'",
    "form-action 'self' https://github.com", "img-src 'self' data:", "font-src 'self'",
    "style-src 'self' 'unsafe-inline'",
    // Next extracts its nonce from the first directive prefixed with script-src.
    `script-src ${scripts}${development ? " 'unsafe-eval'" : ""}`,
    "script-src-attr 'none'",
    development ? "connect-src 'self' ws: wss:" : "connect-src 'self'",
  ].join("; ");
}
