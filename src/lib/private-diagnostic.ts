// Only call this for the authenticated submitter. An excerpt can contain their
// unpublished proof. Never include it in the public queue receipt or server logs.
export function privateDiagnostic(log: string | undefined) {
  if (!log) return undefined;
  const lines = log.split("\n");
  let index = lines.findIndex(line =>
    /(?:Solution|Candidate)\.lean:\d{1,8}:\d{1,8}\b/i.test(line) && /(?:^|[\s:])error:/i.test(line));
  if (index < 0) index = lines.findIndex(line => /^\s*(?:error:|fatal:|panic:|uncaught exception|(?:Check worker allocation|Create worker|Save worker assignment|Read archived proof|Transfer proof files|Confirm proof transfer):|Boat (?:API returned|denied|requires))/i.test(line));
  if (index < 0) return undefined;
  // Include Lean's multi-line explanation, stopping before the next diagnostic.
  const excerpt = [lines[index]];
  for (const line of lines.slice(index + 1, index + 6)) {
    if (!line.trim() || /^\s*(?:error:|warning:|info:|\[)/i.test(line)) break;
    excerpt.push(line);
  }
  return excerpt.join("\n").trim().slice(0, 1200);
}
