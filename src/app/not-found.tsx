import Link from "next/link";
import { ArrowLeft } from "lucide-react";
import { BrandMark } from "@/components/brand-mark";

export default function NotFound() {
  return (
    <main id="main-content" className="not-found-page">
      <BrandMark className="not-found-mark" />
      <span>404</span>
      <h1>Page not found.</h1>
      <p>The requested record or page does not exist.</p>
      <Link className="button button-dark" href="/"><ArrowLeft size={16} /> Return home</Link>
    </main>
  );
}
