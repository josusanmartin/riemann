import Link from "next/link";
import { competitionTrackSchema, type CompetitionTrack } from "@/lib/challenge";
import { competitions } from "@/lib/competitions";
import styles from "./challenge-switcher.module.css";

export function ChallengeSwitcher({ selected }: { selected: CompetitionTrack }) {
  return <nav aria-label="Switch leaderboard" className={`shell ${styles.switcher}`}>
    {competitionTrackSchema.options.map(track => <Link key={track}
      href={competitions[track].board.split("#")[0]} aria-current={selected === track ? "page" : undefined}>
      {competitions[track].shortTitle}
    </Link>)}
  </nav>;
}
