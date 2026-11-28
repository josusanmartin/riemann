import Link from "next/link";
import { ArrowRight, LayoutDashboard, ShieldCheck } from "lucide-react";
import type { ReactNode } from "react";
import styles from "./account-workspace.module.css";

export function WorkspaceHeader({ admin, maintainer, github, children }: {
  admin?: boolean; maintainer: boolean; github: string; children?: ReactNode;
}) {
  return <header className={styles.heading}>
    <nav className={styles.tabs} aria-label="Account views">
      <Link href="/dashboard" aria-current={!admin ? "page" : undefined}><LayoutDashboard size={15} />My dashboard</Link>
      {maintainer && <Link href="/admin" aria-current={admin ? "page" : undefined}><ShieldCheck size={15} />Admin</Link>}
    </nav>
    <div className={styles.title}><div><h1>{admin ? "Verification desk" : "My submissions"}</h1>
      <p>{admin ? "Maintainer" : "GitHub account"} · @{github}</p></div>{children}</div>
  </header>;
}

export function Metrics({ items }: { items: { value: ReactNode; label: string }[] }) {
  return <dl className={styles.metrics}>{items.map(({ value, label }) => <div key={label}><dt>{label}</dt><dd>{value}</dd></div>)}</dl>;
}

export function NewSubmissionLink() {
  return <Link className="button button-dark" href="/submit">Submit a proof <ArrowRight size={16} /></Link>;
}

export function resultLabel(status: string) {
  switch (status) {
    case "promoted": return "Published";
    case "rejected": return "Unsuccessful";
    case "publication-blocked": return "Publication blocked";
    case "superseded": return "Superseded";
    case "archived": return "Archived";
    default: return status;
  }
}
