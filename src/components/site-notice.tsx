// Operators set SITE_NOTICE in Vercel and redeploy to show a site-wide banner,
// for example during a verifier upgrade. Unset it and redeploy to remove it.
export function SiteNotice() {
  const message = process.env.SITE_NOTICE?.trim();
  if (!message) return null;
  return (
    <div className="site-notice" role="status">
      <p>{message}</p>
    </div>
  );
}
