import type { Metadata, Viewport } from "next";
import { Inter } from "next/font/google";
import { Analytics } from "@vercel/analytics/next";
import { SiteHeader } from "@/components/site-header";
import { SiteFooter } from "@/components/site-footer";
import { truncateDecimalString } from "@/components/format";
import { getCurrentRecord } from "@/lib/records";
import { siteUrl } from "@/lib/site";
import "./globals.css";

const inter = Inter({ subsets: ["latin"], display: "swap", variable: "--font-inter" });
const current = getCurrentRecord();
const currentPercent = truncateDecimalString(current.scorePercent, 2);

export const metadata: Metadata = {
  metadataBase: new URL(siteUrl),
  title: {
    default: `Riemann zeta function — at least ${currentPercent}% of zeros on the critical line`,
    template: "%s · Riemann zeta function",
  },
  description:
    "A machine-checked record of the largest proven proportion of nontrivial Riemann zeta zeros on the critical line. New results are submitted as Lean proofs and rechecked before they are published.",
  applicationName: "Riemann zeta function",
  keywords: ["Riemann zeta", "Lean 4", "formal verification", "analytic number theory", "critical line"],
  openGraph: {
    type: "website",
    url: siteUrl,
    siteName: "Riemann zeta function",
    title: "Riemann zeta function — critical-line bound record",
    description:
      "The current record for the proportion of Riemann zeta zeros proven to lie on the critical line, verified in Lean and open to new submissions.",
  },
  twitter: {
    card: "summary_large_image",
    title: "Riemann zeta function",
    description: "The verified record for critical-line zeros of the Riemann zeta function.",
  },
};

export const viewport: Viewport = {
  colorScheme: "light",
  themeColor: "#0b211c",
};

export default function RootLayout({ children }: Readonly<{ children: React.ReactNode }>) {
  return (
    <html lang="en" className={inter.variable}>
      <body>
        <a className="skip-link" href="#main-content">Skip to content</a>
        <SiteHeader />
        {children}
        <SiteFooter />
        {process.env.VERCEL === "1" && <Analytics />}
      </body>
    </html>
  );
}
