import type { Metadata } from "next";
import Link from "next/link";
import { readFileSync } from "node:fs";
import { CodeBlock } from "@/components/code-block";
import { repositoryUrl } from "@/lib/site";
import styles from "../../challenges.module.css";

export const metadata: Metadata = { title: "Formalize Xu’s simple-zero theorem", description: "An open Lean formalization problem for Theorem 1 of Yuanda Xu’s November 2026 preprint." };

export default function XuTheorem() {
  return <main id="main-content" className={`shell section-space ${styles.directory}`}>
    <Link href="/challenges/simple-zeros" className="text-link">← Simple zeros</Link>
    <h1>Formalize Xu’s simple-zero theorem</h1>
    <p className={styles.lede}>Assuming RH, at least 71.27406684% of nontrivial zeta zeros are simple in the cumulative limit. The challenge is to formalize this theorem in Lean.</p>
    <div className={styles.actions}><a className="button button-dark" href={`${repositoryUrl}/issues/new?template=simple-zeros.yml`}>Submit a project for review</a>
      <a className="text-link" href="/templates/XuSimpleZeros.lean" download>Download the Lean statement</a></div>
    <h2>The target</h2>
    <p>Prove Theorem 1 at its stated precision for positive ordinates up to height T. The abstract truncates the percentage. The paper gives a separate theorem about distinct zeros. <a className="text-link" href="https://arxiv.org/html/2611.34546v1#S1.SS2">Read Xu’s theorems</a></p>
    <CodeBlock label="XuSimpleZeros.lean">{readFileSync("public/templates/XuSimpleZeros.lean", "utf8")}</CodeBlock>
    <h2>Where to start</h2>
    <p>Bui and Heath-Brown proved 19/27 (about 70.37%) under RH. Xu adds a local test for multiple zeros and mixed moments of Dirichlet polynomials. Appendix A describes the rational certificate data. A formalization needs to connect those finite calculations to the asymptotic zero count. <a className="text-link" href="https://arxiv.org/abs/1302.5018">Bui and Heath-Brown</a> · <a className="text-link" href="https://arxiv.org/html/2611.34546v1">Xu’s Appendix A</a></p>
    <h2>What to submit</h2>
    <p>Share an immutable source revision, pinned Lean dependencies and clean build instructions. Prove the analytic estimates and the rational certificate, or import them from checked proofs. Document the final theorem’s axiom dependencies. The accepted logical axioms are propext, Classical.choice and Quot.sound. RH may be an explicit hypothesis.</p>
    <p>The fixed target only requires (0, T]. A separate <Link className="text-link" href="/challenges/simple-zeros">ranked submission</Link> also proves the dyadic estimate and will go through the automated verifier once ranked uploads open.</p>
  </main>;
}
