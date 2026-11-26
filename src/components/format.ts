/**
 * Truncate (never round) an exact non-negative decimal string.
 * Certified lower bounds must not display above their proven value, so
 * presentation always truncates; rounding half-up would overstate the theorem.
 */
export function truncateDecimalString(value: string, places: number): string {
  const dot = value.indexOf(".");
  if (dot === -1) return value;
  if (places <= 0) return value.slice(0, dot);
  const fraction = value.slice(dot + 1).replace(/0+$/, "").slice(0, places);
  return fraction ? value.slice(0, dot + 1) + fraction : value.slice(0, dot);
}
