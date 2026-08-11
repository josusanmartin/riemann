import Link from "next/link";
import { Github, ExternalLink } from "lucide-react";
import { BrandMark } from "@/components/brand-mark";
import { repositoryUrl } from "@/lib/site";

export function SiteFooter() {
  return (
    <footer className="site-footer">
      <div className="shell footer-grid">
        <div>
          <Link className="brand footer-brand" href="/">
            <BrandMark className="brand-mark" />
            <span>Riemann<span className="brand-dot">.fail</span></span>
          </Link>
          <p>An open arena for machine-checked progress in analytic number theory.</p>
          <p className="footer-note">Independent community project — not affiliated with Anthropic or the authors of Zeta23.</p>
        </div>
        <div className="footer-links">
          <div>
            <span className="footer-label">Arena</span>
            <Link href="/challenge">Challenge contract</Link>
            <Link href="/methodology">Trust & verification</Link>
            <Link href="/submit">Submit a proof</Link>
            <Link href="/submissions">All submissions</Link>
          </div>
          <div>
            <span className="footer-label">Source</span>
            <a href={repositoryUrl} target="_blank" rel="noreferrer">
              <Github size={14} /> GitHub
            </a>
            <a href="https://github.com/anthropics/zeta-23-lean" target="_blank" rel="noreferrer">
              Zeta23 <ExternalLink size={13} />
            </a>
          </div>
        </div>
      </div>
      <div className="shell footer-bottom">
        <span>Built in public · Exact arithmetic · No numerical claims without proofs</span>
        <span>MIT site · Apache-2.0 submissions</span>
      </div>
    </footer>
  );
}
