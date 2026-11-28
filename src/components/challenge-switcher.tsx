import Link from "next/link";
import type { CompetitionTrack } from "@/lib/challenge";
import styles from "./challenge-switcher.module.css";

export function ChallengeSwitcher({ selected }: { selected: CompetitionTrack }) {
  return <nav aria-label="Switch leaderboard" className={`shell ${styles.switcher}`}>
    <Link href="/" aria-current={selected === "critical-line" ? "page" : undefined}>Distinct zeros</Link>
    <Link href="/challenges/simple-zeros" aria-current={selected === "simple-zeros" ? "page" : undefined}>Simple zeros</Link>
  </nav>;
}
