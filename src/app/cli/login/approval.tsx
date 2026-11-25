"use client";
import { useState } from "react";
import type { Pairing } from "@/lib/cli-login";
import { approveCliLogin } from "./actions";

export function Approval({ pairing }: { pairing: Pairing }) {
  const [approval, setApproval] = useState("");
  const [busy, setBusy] = useState(false);
  const [copied, setCopied] = useState(false);
  const [error, setError] = useState("");
  async function approve() {
    setBusy(true);
    try {
      const result = await approveCliLogin(pairing);
      if (!result.approval) { setError(result.error ?? "Approval failed."); return; }
      setApproval(result.approval);
      if (pairing.port) {
        const url = new URL(`http://127.0.0.1:${pairing.port}/callback`);
        url.searchParams.set("state", pairing.challenge);
        // The fragment stays in the browser until the local landing page
        // posts it to the CLI. Nothing secret is sent as a query parameter.
        url.hash = new URLSearchParams({ approval: result.approval }).toString();
        window.location.assign(url.href);
      }
    } catch { setError("Could not approve this login. Refresh the page and try again."); }
    finally { setBusy(false); }
  }
  if (approval) return <div>
    <p>{pairing.port ? "Returning to the CLI. If the local browser cannot connect, start a new login with --manual." : "Run riemann login --finish on the agent host and paste this approval when prompted."}</p>
    {!pairing.port && <>
      <textarea aria-label="CLI approval" readOnly rows={4} value={approval} onFocus={e => e.target.select()} />
      <button type="button" className="button button-ghost-light" onClick={async () => {
        try { await navigator.clipboard.writeText(approval); setCopied(true); }
        catch { setError("Select the approval above and copy it."); }
      }}>{copied ? "Copied" : "Copy approval"}</button>
      {error && <p role="status">{error}</p>}
    </>}
  </div>;
  return <div>
    <button type="button" className="button button-lime" disabled={busy} onClick={approve}>{busy ? "Approving…" : "Approve CLI login"}</button>
    {error && <p role="alert">{error}</p>}
  </div>;
}
