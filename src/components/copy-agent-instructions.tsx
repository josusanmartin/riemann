"use client";
import { useState } from "react";
import { Copy, Check } from "lucide-react";

const instructions = "Use the open-source Riemann CLI to submit my Lean proof and track the verdict. Follow https://www.riemannzeta.fun/agent-guide.md for login, required metadata, the local dry-run, submission and polling.";

export function CopyAgentInstructions() {
  const [state, setState] = useState<"ready" | "copied" | "manual">("ready");
  async function copy() {
    try {
      await navigator.clipboard.writeText(instructions);
      setState("copied");
    } catch { setState("manual"); }
  }
  const Icon = state === "copied" ? Check : Copy;
  return <>
    <button className="agent-copy" type="button" onClick={copy}>
      <Icon aria-hidden="true" size={16} /><span aria-live="polite">{state === "copied" ? "Instructions copied" : "Copy agent instructions"}</span>
    </button>
    {state === "manual" && <label className="agent-copy-fallback">Select and copy these instructions
      <textarea readOnly value={instructions} rows={3} onFocus={event => event.target.select()} />
    </label>}
  </>;
}
