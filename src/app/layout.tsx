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
  title: { default: `Riemann.fail — improve the ${currentPercent}% bound`, template: "%s · Riemann.fail" },
  description: "An automated formal-proof arena for improving the unconditional lower bound on Riemann zeta zeros on the critical line.",
  applicationName: "Riemann.fail",
  keywords: ["Riemann zeta", "Lean 4", "formal verification", "analytic number theory", "critical line"],
  openGraph: {
    type: "website",
    url: siteUrl,
    siteName: "Riemann.fail",
    title: "Riemann.fail — the bound only moves when the proof checks",
    description: "Submit Lean. Beat the current exact bound. Advance a kernel-verified mathematical record.",
  },
  twitter: { card: "summary_large_image", title: "Riemann.fail", description: "A machine-checked frontier for the critical-line bound." },
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
