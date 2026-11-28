import type { Metadata } from "next";
import Link from "next/link";
import { notFound } from "next/navigation";
import {
  ArrowLeft,
  ArrowUpRight,
  BadgeCheck,
  BookOpen,
  ChevronDown,
} from "lucide-react";
import { compactReplay, compactCertificateUrl } from "@/lib/compact-replay";
import { getRecord, records } from "@/lib/records";
import { formatRecordTime, recordVerifiedAt } from "@/lib/record-times";
import { recordPresentation } from "./presentation";
import styles from "./record.module.css";

type PageProps = { params: Promise<{ id: string }> };

export function generateStaticParams() {
  return records.map((record) => ({ id: record.id }));
}

export async function generateMetadata({
  params,
}: PageProps): Promise<Metadata> {
  const record = getRecord((await params).id);
  if (!record) return { title: "Record not found" };
  const { score, heading, status } = recordPresentation(record);
  const title = `At least ${score} · ${heading}`;
  const description = `${record.author} · ${status}. ${record.method}`;
  const url = `/submissions/${record.id}`;
  const image = {
    url: `${url}/share-image?v=${compactCertificateUrl(record) ? 4 : 3}`,
    width: 1200,
    height: 630,
    alt: `${title} · ${record.author}`,
  };
  return {
    title,
    description,
    alternates: { canonical: url },
    openGraph: {
      title,
      description,
      url,
      siteName: "Riemann zeta function",
      type: "article",
      images: [image],
    },
    twitter: {
      card: "summary_large_image",
      title,
      description,
      images: [image],
    },
  };
}

export default async function SubmissionPage({ params }: PageProps) {
  const record = getRecord((await params).id);
  if (!record) notFound();
  const { score, heading, status } = recordPresentation(record);
  const verifiedAt = recordVerifiedAt(record);
  const Badge = record.formalVerification ? BadgeCheck : BookOpen;
  const fraction = record.exactRational;
  const powerOfTen = fraction && /^10{7,}$/.test(fraction.denominator)
    ? fraction.denominator.length - 1
    : null;
  const certificateUrl = compactCertificateUrl(record);
  const sourceIsManifest = record.sourceUrl.endsWith("/submission.json");

  return (
    <main id="main-content" className={`submission-sheet ${styles.sheet}`}>
      <Link className={styles.back} href={record.track === "simple-zeros" ? "/challenges/simple-zeros#leaderboard" : "/#leaderboard"}>
        <ArrowLeft size={14} /> Leaderboard
      </Link>
      <article className={styles.card}>
        <header className={styles.hero}>
          <div className={styles.topline}>
            <span className={styles.badge}>
              <Badge size={16} /> {status}
            </span>
            <time dateTime={verifiedAt ?? record.date}>
              {formatRecordTime(record, verifiedAt)}
            </time>
          </div>
          <div className={styles.result}>
            <div className={styles.score} aria-label={`Lower bound ${score}`}>
              {score.slice(0, -1)}
              <span>%</span>
            </div>
            <div className={styles.credit}>
              <h1>{heading}</h1>
              <p>
                {record.author}
                {record.github && (
                  <a href={`https://github.com/${record.github}`}>
                    @{record.github}
                  </a>
                )}
              </p>
            </div>
          </div>
          <div className={styles.actions}>
            <a
              className={styles.primary}
              href={record.proofUrl ?? record.sourceUrl}
            >
              {record.proofUrl ? "View proof" : "View source"}{" "}
              <ArrowUpRight size={16} />
            </a>
            {record.proofUrl && record.sourceUrl !== record.proofUrl && (
              <a className={styles.secondary} href={record.sourceUrl}>
                {sourceIsManifest ? "Submission manifest" : "Research paper"}{" "}
                <ArrowUpRight size={14} />
              </a>
            )}
          </div>
        </header>
        <div className={styles.body}>
          <dl className={styles.facts}>
            <div>
              <dt>Exact bound κ</dt>
              <dd className={styles.exact}>
                {fraction ? (
                  <span>
                    {fraction.numerator} / {powerOfTen === null
                      ? fraction.denominator
                      : <>10<sup>{powerOfTen}</sup></>}
                  </span>
                ) : record.exactExpression}
              </dd>
            </div>
            <div>
              <dt>Method</dt>
              <dd>{record.method}</dd>
            </div>
            {record.rhFoundationCommit && (
              <div>
                <dt>Admission foundation</dt>
                <dd>
                  <Link href="/methodology">{record.rhFoundationCommit === compactReplay.foundationCommit ? "Compact RH proof replayed" : "Published RH premise"}</Link>
                </dd>
              </div>
            )}
            {certificateUrl && (
              <div>
                <dt>Compact RH replay</dt>
                <dd>
                  Lean and nanoda checked both bounds with the proof of RH included.
                  {" "}<a href={certificateUrl}>{record.id === compactReplay.recordId ? "Certificate and replay instructions" : "Verification receipt"}</a>
                </dd>
              </div>
            )}
            {record.model && (
              <div>
                <dt>Model</dt>
                <dd>{record.model}</dd>
              </div>
            )}
            {record.harness && (
              <div>
                <dt>Harness</dt>
                <dd>{record.harness}</dd>
              </div>
            )}
          </dl>
          <details className={styles.details}>
            <summary>
              Submission notes and proof expression <ChevronDown size={17} />
            </summary>
            <code>κ = {record.exactExpression}</code>
            <p>{record.summary}</p>
            {record.rhFoundationCommit && (
              <p>
                RH foundation revision <code>{record.rhFoundationCommit}</code>
              </p>
            )}
            {record.independentReview ? (
              <p>
                Independent review by{" "}
                <a href={record.independentReview.url}>
                  {record.independentReview.reviewer}
                </a>{" "}
                · {record.independentReview.date}.{" "}
                {record.independentReview.summary}
              </p>
            ) : (
              <p>No independent expert review has been recorded.</p>
            )}
          </details>
        </div>
      </article>
    </main>
  );
}
