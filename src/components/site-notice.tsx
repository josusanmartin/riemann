export function SiteNotice() {
  const message = process.env.SITE_NOTICE?.trim();
  if (!message) return null;
  return (
    <div className="site-notice" role="status">
      <p>{message}</p>
    </div>
  );
}
