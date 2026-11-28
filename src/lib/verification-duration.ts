import limits from "../../boat/compact/time-limits.json";

function duration(seconds: number) {
  const hours = Math.floor(seconds / 3600);
  const minutes = Math.floor((seconds % 3600) / 60);
  const remainder = seconds % 60;
  return [[hours, "hour"], [minutes, "minute"], [remainder, "second"]]
    .filter(([value]) => value !== 0)
    .map(([value, unit]) => `${value} ${unit}${value === 1 ? "" : "s"}`).join(" ");
}

export const verificationDuration = duration(limits.verificationSeconds);
export const workerDuration = duration(limits.workerLifetimeSeconds);
