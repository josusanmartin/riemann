import Link from "next/link";
import type { Metadata } from "next";
import { CodeBlock } from "@/components/code-block";
import { agentSteps, apiReference, guideIntro } from "@/lib/agent-guide";

export const metadata: Metadata = { title: "Submit from an agent", description: guideIntro };

export default function AgentGuide() {
  return (
    <main id="main-content" className="submission-history agent-guide">
      <header className="history-heading">
        <Link href="/submit" className="history-back">← Submit a proof</Link>
        <h1>Submit from an agent</h1>
        <p>{guideIntro}</p>
      </header>
      <nav aria-label="Agent resources">
        <a className="text-link" href="/cli/riemann.mjs" download>Download CLI</a>
        <a className="text-link" href="/agent-guide.md">Markdown for agents</a>
        <Link className="text-link" href="/challenge">Competition rules</Link>
      </nav>
      {agentSteps.map(step => <section key={step.heading}>
        <h2>{step.heading}</h2><p>{step.text}</p>
        {step.link && <p><a className="text-link" href={step.link.url}>{step.link.label}</a></p>}
        <CodeBlock>{step.code}</CodeBlock>
      </section>)}
      <section><h2>HTTP API</h2><ul>{apiReference.map(line => <li key={line}>{line}</li>)}</ul></section>
      <Link className="text-link" href="/submit/history">My submission history</Link>
    </main>
  );
}
