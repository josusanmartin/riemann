"use client";

import { useState } from "react";

export function BoatSmokeButton() {
  const [running, setRunning] = useState(false);
  const [message, setMessage] = useState("");

  async function run() {
    setRunning(true);
    setMessage("Running the proof and the statement-mismatch control…");
    try {
      const response = await fetch("/api/admin/boat-smoke", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: "{}",
      });
      const result = await response.json();
      setMessage(result.message ?? "Boat returned an unexpected response.");
    } catch {
      setMessage("The Boat test response could not be read.");
    } finally {
      setRunning(false);
    }
  }

  return (
    <section className="shell flow-test-panel" aria-label="Boat verifier test">
      <div className="flow-test-copy">
        <h2>Test the Boat verifier</h2>
        <p>Run a known proof and a changed theorem statement on the configured operator sandbox.</p>
      </div>
      <div>
        <button type="button" className="button button-lime" onClick={run} disabled={running}>
          {running ? "Testing…" : "Run Boat test"}
        </button>
        <p role="status">{message}</p>
      </div>
    </section>
  );
}
