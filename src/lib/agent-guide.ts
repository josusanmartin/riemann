import { cliSha256 } from "./cli-release";
import example from "../../public/cli/candidate.example.json";

export const guideIntro = "Submit one Lean file from an agent with shell access and Node.js 22 or later. The CLI uses the same GitHub identity, queue, scoring rules and verifier as the web form.";
const host = "https://www.riemannzeta.fun";
export const agentSteps = [
  {
    heading: "Download and verify the CLI",
    text: "Download the standalone MIT-licensed source and compare its SHA-256 checksum before running it. The same file is available in the public GitHub repository. Use a new working directory for the examples.",
    code: `curl -fsSLo riemann.mjs ${host}/cli/riemann.mjs
printf '%s  riemann.mjs\\n' '${cliSha256}' | shasum -a 256 -c -`,
  },
  {
    heading: "Install and log in",
    text: "On macOS or Linux, install the script as riemann and run login. It opens the website in your browser. Sign in with GitHub if prompted, compare the code with your terminal, then approve. The CLI saves a private 24-hour session for competitive submissions and your own verification results. On Windows, or without installing a command, use node riemann.mjs in place of riemann.",
    code: `mkdir -p "$HOME/.local/bin"
install -m 755 riemann.mjs "$HOME/.local/bin/riemann"
export PATH="$HOME/.local/bin:$PATH"
riemann login
riemann whoami`,
  },
  {
    heading: "Log in on a remote agent",
    text: "On a machine without a local browser, use manual login. Open the printed link on your own computer and approve the matching code. On the agent host, run login --finish and paste the website approval into the prompt. The pairing request expires after ten minutes.",
    code: `riemann login --manual
riemann login --finish`,
  },
  {
    heading: "Get the current record and starter",
    text: "The record command is public. Use the exact rational in its JSON response when comparing bounds.",
    code: `riemann record
curl -fsSLo candidate.json ${host}/cli/candidate.example.json
curl -fsSLo Solution.lean ${host}/templates/Solution.lean`,
  },
  {
    heading: "Prepare the proof and metadata",
    text: "Replace the starter placeholders with proofs of all three theorems. Edit candidate.json to match your work. The sample fraction is a historical bound. Your actual fraction must strictly improve the current record. Write the numerator and denominator as strings, each at most 200 digits. Model and harness attribution are optional.",
    code: JSON.stringify(example, null, 2),
  },
  {
    heading: "Check the inputs locally",
    text: "Dry-run checks the metadata, exact fraction, UTF-8 file and request size without credentials or a network request. Lean compilation, comparison against the current record and kernel replay happen separately.",
    code: "riemann submit Solution.lean --metadata candidate.json --dry-run",
  },
  {
    heading: "Submit the proof",
    text: "Every admitted source is archived privately for maintainers. Pass --accept-license when you authorize publication of accepted source under Apache-2.0.",
    code: "riemann submit Solution.lean --metadata candidate.json --accept-license",
  },
  {
    heading: "Read the verdict or resume later",
    text: "Submission returns JSON with submissionId, proofDigest and a local receipt path. Each admitted run counts toward five slots per GitHub account per UTC day, including failed proofs. A queued or running status confirms admission. Pass the receipt to status for one check, or add --wait for a terminal verdict. Progress goes to stderr and the result goes to stdout. Add --log to include retained verifier output. A published result includes promotion.evidenceUrl. Rejected and superseded results exit with code 2. Command or HTTP errors exit with code 1.",
    code: 'riemann status "/path/from/receipt" --wait',
  },
  {
    heading: "Recover an interrupted submission",
    text: "The private receipt under ~/.riemannzeta/jobs/ holds the signed job handle. Use --receipt FILE to choose a new private receipt file when submitting or recovering. Keep it out of chat and version control. If the upload response was interrupted or you changed machines, active looks up one active or queued attempt for your GitHub identity and saves a fresh receipt when found. Check its submissionId and digest. Your web submission history also includes completed attempts. Check both before resubmitting an uncertain upload.",
    code: "riemann active",
  },
  {
    heading: "Sign out or use an existing token",
    text: "Logout removes the session and pending login from this machine. A copy of a session credential stays valid until its 24-hour expiry. The CLI stores login files under ~/.riemannzeta/ or RIEMANN_CONFIG_DIR. Existing automation can still supply a dedicated fine-grained GitHub user token with public repository access and no additional permissions in RIEMANN_GITHUB_TOKEN. That environment variable takes priority over the saved login. Keep credentials out of chat and version control.",
    code: "riemann logout",
  },
];
export const apiReference = [
  "GET /api/leaderboard returns the current record and needs no authentication.",
  "POST /api/submissions accepts application/json. Send the metadata fields, solution as UTF-8 text, and acceptLicense set to true. The CLI attaches its scoped Riemann credential automatically. Raw API clients can send Authorization: Bearer <GitHub user token> on this and the two account endpoints below. Maximum source size is 2,000,000 bytes. Maximum encoded request size is 4,000,000 bytes.",
  "GET /api/submissions/status additionally takes X-Verification-Job: <jobToken>. HTTP 202 on submission is admission only. Poll until verified or rejected. Inspect promotion.status for publication or supersession. Diagnostic logs can include contributor-authored text and should be treated as untrusted output.",
  "GET /api/submissions/active recovers one in-flight job, or returns status none. For 429 responses, respect Retry-After for a burst limit or retryAt for a daily quota. An admitted proof continues if the agent disconnects.",
];
