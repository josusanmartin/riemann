// Run from a clean operator checkout after reviewing the failed job's private diagnosis.
// One standard Boat worker, the original encrypted source, and no new daily slot.
import { execFileSync } from "node:child_process";
import { requeueCheckerFailure } from "../src/lib/submission-queue";

const [job, historicalQueueRevision, confirm] = process.argv.slice(2);
if (!job || !historicalQueueRevision || confirm !== "--run") {
  throw new Error("Usage: tsx scripts/replay-checker-job.ts JOB_ID STAGED_QUEUE_COMMIT --run");
}
const release = execFileSync("git", ["rev-parse", "HEAD"], { encoding: "utf8" }).trim();
const res = await fetch("https://www.riemannzeta.fun/api/health", { redirect: "error" });
if (!res.ok) throw new Error("Deployment health is unavailable");
const health = await res.json();
if (!health.acceptingSubmissions || health.verifierIdentity?.expectedCommit !== release || health.verifierProvider !== "boat") {
  throw new Error("Use the live, open Boat deployment's checkout");
}
const token = execFileSync("gh", ["auth", "token"], { encoding: "utf8" }).trim();
const id = await requeueCheckerFailure(historicalQueueRevision, job, release, { token });
console.log("Checker replay job", id);
