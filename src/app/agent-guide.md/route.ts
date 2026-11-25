import { agentSteps, apiReference, guideIntro } from "@/lib/agent-guide";

export const dynamic = "force-static";
export function GET() {
  const sections = agentSteps.map(step => `## ${step.heading}\n\n${step.text}${step.link ? `\n\n[${step.link.label}](${step.link.url})` : ""}\n\n\`\`\`\n${step.code}\n\`\`\``);
  const body = ["# Submit from an agent", guideIntro, ...sections,
    "## HTTP API", apiReference.map(line => "- " + line).join("\n"),
    "Rules: https://www.riemannzeta.fun/challenge\nHistory: https://www.riemannzeta.fun/submit/history",
  ].join("\n\n");
  return new Response(body + "\n", { headers: { "Content-Type": "text/markdown; charset=utf-8" } });
}
