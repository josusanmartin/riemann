import type { QueuedVerificationJob } from "./submission-queue";

export const setupLimitMs = 3 * 60_000;
export const setupRetryMs = 10_000;

// Nov 25 queue history: 25 assigned Boat workers, median 3 s to allocation
// and 4 s to staging. 21 accepted runs had a median of 16 min after staging.
export function boatProgress(job: QueuedVerificationJob) {
  const b = job.boat!;
  const stage = b.uploaded ? "checking" : b.workerId ? "staging" : "allocation";
  const info = {
    allocation: "Requesting a Boat worker. The median assignment took 3 seconds. Worker setup has a 3-minute retry window.",
    staging: "Sending the saved proof to the assigned worker. The median upload took 4 seconds.",
    checking: "The worker checks the submitted source, links the compact RH proof, then replays the exported certificate in two kernels. Replay time depends on the proof.",
  };
  const diagnostic = !b.uploaded && b.setupIssue ? ` Last setup issue: ${b.setupIssue}.` : "";
  return {
    status: "running" as const, stage,
    stageStartedAt: (b.uploaded ? b.stagedAt : b.workerId ? b.assignedAt : b.startedAt) ?? null,
    proofDigest: job.proofDigest,
    message: info[stage] + diagnostic + (b.memoryReplayOf ? " This is the larger memory-retry worker." : ""),
  };
}
