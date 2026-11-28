import type { CompetitionTrack } from "./challenge";

// Public navigation and presentation. The verifier owns the trusted Lean targets.
export const competitions = {
  "critical-line": {
    title: "Distinct zeros on the critical line", shortTitle: "Distinct zeros",
    description: "Count each location on the line once, including locations where several zeros coincide.",
    board: "/#leaderboard", rules: "/challenge", starter: "/templates/Solution.lean",
  },
  "simple-zeros": {
    title: "Simple zeros", shortTitle: "Simple zeros",
    description: "Count only zeros of multiplicity one. A double zero contributes zero to this count.",
    board: "/challenges/simple-zeros", rules: "/challenges/simple-zeros", starter: "/templates/Simple.lean",
  },
} satisfies Record<CompetitionTrack, {
  title: string; shortTitle: string; description: string; board: string; rules: string; starter: string;
}>;
