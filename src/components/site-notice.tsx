import Link from "next/link";

// A live operational notice takes precedence over the contributor announcement.
export function SiteNotice() {
  const message = process.env.SITE_NOTICE?.trim();
  if (message) {
    return (
      <div className="site-notice" role="status">
        <p>{message}</p>
      </div>
    );
  }

  return (
    <aside className="site-notice contributor-notice" aria-label="Notice to contributors">
      <p><strong>Contributor update · November 21, 2026</strong></p>
      <p>
        Thank you to everyone who raised the bound to{" "}
        <Link href="/submissions/bakken-ten-hw-one-unit">67.3639%</Link> without assuming RH.
        The <Link href="/submissions/critical-line-669-800">83.625% record</Link> uses Alpöge’s
        published RH theorem as a trusted premise. Each earlier proof keeps its original
        verification history. <Link href="/methodology">Read the updated rules.</Link>
      </p>
    </aside>
  );
}
