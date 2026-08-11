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
            <span>Riemann <span className="brand-sub">zeta function</span></span>
          </Link>
          <p>A machine-checked record of unconditional lower bounds for zeros of the Riemann zeta function on the critical line.</p>
          <p className="footer-note">Independent project, not affiliated with Anthropic or the authors of Zeta23.</p>
        </div>
        <div className="footer-links">
          <div>
            <span className="footer-label">Pages</span>
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
            <a href="https://www.anthropic.com/research/riemann-zeta" target="_blank" rel="noreferrer">
              Anthropic article <ExternalLink size={13} />
            </a>
          </div>
        </div>
      </div>
      <div className="shell footer-bottom">
        <span>Records are ordered by exact arithmetic; every published bound has a machine-checked proof.</span>
        <span>MIT site · Apache-2.0 submissions</span>
      </div>
    </footer>
  );
}
