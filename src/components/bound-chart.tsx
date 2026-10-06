import type { RecordEntry } from "@/lib/challenge";
import { truncateDecimalString } from "@/components/format";
import { formatRecordTime, recordVerifiedAt } from "@/lib/record-times";

const START_YEAR = 1974;
const END_YEAR = 2026;
const MIN_SCORE = 0.3;
const MAX_SCORE = 0.7;
const Y_TICKS = [0.3, 0.4, 0.5, 0.6, 0.7];

type Geometry = {
  width: number;
  height: number;
  padding: { top: number; right: number; bottom: number; left: number };
  xTicks: number[];
};

const WIDE: Geometry = {
  width: 760,
  height: 310,
  padding: { top: 32, right: 34, bottom: 46, left: 60 },
  xTicks: [1974, 1989, 2000, 2010, 2020, 2026],
};

const COMPACT: Geometry = {
  width: 400,
  height: 330,
  padding: { top: 36, right: 22, bottom: 48, left: 52 },
  xTicks: [1974, 2000, 2026],
};

type ChartPoint = { record: RecordEntry; year: number; score: number; recordsThatYear: number };

function pointLabel(point: ChartPoint, isCurrent: boolean): string {
  return `at least ${truncateDecimalString(point.record.scorePercent, isCurrent ? 2 : 1)}%`;
}

function ChartSvg({
  points,
  geometry,
  variant,
}: {
  points: ChartPoint[];
  geometry: Geometry;
  variant: "wide" | "compact";
}) {
  const { width, height, padding, xTicks } = geometry;
  const x = (year: number) =>
    padding.left + ((year - START_YEAR) / (END_YEAR - START_YEAR)) * (width - padding.left - padding.right);
  const y = (score: number) =>
    padding.top + ((MAX_SCORE - score) / (MAX_SCORE - MIN_SCORE)) * (height - padding.top - padding.bottom);

  // A record is a step function: each bound holds until the next one is proved.
  const line = points
    .map((point, index) =>
      index === 0 ? `M${x(point.year)},${y(point.score)}` : `H${x(point.year)} V${y(point.score)}`,
    )
    .join(" ");

  const summary = points
    .map((point, index) => `${point.year}: ${pointLabel(point, index === points.length - 1)} (${point.record.author})`)
    .join("; ");

  return (
    <svg
      className={`bound-chart bound-chart-${variant}`}
      viewBox={`0 0 ${width} ${height}`}
      role="img"
      aria-label={`Certified critical-line lower bound by year. ${summary}`}
    >
      {Y_TICKS.map((tick) => (
        <g key={tick}>
          <line x1={padding.left} y1={y(tick)} x2={width - padding.right} y2={y(tick)} className="chart-grid" />
          <text x={padding.left - 12} y={y(tick) + 4} textAnchor="end" className="chart-label">
            {Math.round(tick * 100)}%
          </text>
        </g>
      ))}
      {xTicks.map((tick, index) => (
        <text
          key={tick}
          x={x(tick)}
          y={height - 14}
          textAnchor={index === 0 ? "start" : index === xTicks.length - 1 ? "end" : "middle"}
          className="chart-label"
        >
          {tick}
        </text>
      ))}
      <path d={line} className="chart-line" />
      {points.map((point, index) => {
        const { record, year, score } = point;
        const isCurrent = index === points.length - 1;
        return (
          <g key={record.id}>
            <title>{`${year} · ${record.author} · ${pointLabel(point, isCurrent)} · ${record.method}${
              point.recordsThatYear > 1 ? ` · best of ${point.recordsThatYear} records in ${year}` : ""
            }`}</title>
            <circle
              cx={x(year)}
              cy={y(score)}
              r={isCurrent ? 8 : 5}
              className={isCurrent ? "chart-point chart-point-current" : "chart-point"}
            />
            <text
              x={x(year)}
              y={y(score) - 15}
              textAnchor={index === 0 ? "start" : isCurrent ? "end" : "middle"}
              className="chart-value"
            >
              {truncateDecimalString(record.scorePercent, isCurrent ? 2 : 1)}%
            </text>
          </g>
        );
      })}
    </svg>
  );
}

type RacePoint = { record: RecordEntry; time: number; percent: number; when: string };

const HOUR = 60 * 60 * 1_000;
const DAY = 24 * HOUR;
const dayLabel = new Intl.DateTimeFormat("en-US", { month: "short", day: "numeric", timeZone: "UTC" });

// Smallest "nice" percentage-point step that keeps the axis to about five intervals.
function niceStep(span: number): number {
  const steps = [0.005, 0.01, 0.02, 0.025, 0.05, 0.1, 0.2, 0.25, 0.5, 1];
  return steps.find((step) => span / step <= 5) ?? 1;
}

function percentLabel(value: number, step: number): string {
  const decimals = Math.max(0, Math.ceil(-Math.log10(step) - 1e-9));
  return `${value.toFixed(decimals)}%`;
}

/**
 * The 1974–2026 axis compresses every riemann.fun record into one point, so
 * this zooms in on the kernel-verified race: one step per accepted record,
 * entering from the Zeta23 baseline it started from.
 */
function RaceChartSvg({
  baseline,
  points,
  geometry,
  variant,
}: {
  baseline: RacePoint;
  points: RacePoint[];
  geometry: Geometry;
  variant: "wide" | "compact";
}) {
  const { width, height, padding } = geometry;
  const start = Math.floor(points[0].time / DAY) * DAY;
  const last = points.at(-1)!;
  const end = last.time + Math.max(6 * HOUR, (last.time - start) * 0.06);
  const low = Math.min(baseline.percent, ...points.map((point) => point.percent));
  const high = Math.max(...points.map((point) => point.percent));
  const step = niceStep(high - low);
  const yMin = Math.floor((low - step * 0.25) / step) * step;
  const yMax = Math.ceil((high + step * 0.25) / step) * step;
  const yTicks = Array.from({ length: Math.round((yMax - yMin) / step) + 1 }, (_, i) => yMin + i * step);
  const xTicks: number[] = [];
  for (let day = start; day <= end; day += DAY) xTicks.push(day);
  const shownXTicks = variant === "compact" && xTicks.length > 4
    ? xTicks.filter((_, index) => index % Math.ceil(xTicks.length / 4) === 0)
    : xTicks;

  const x = (time: number) =>
    padding.left + ((time - start) / (end - start)) * (width - padding.left - padding.right);
  const y = (percent: number) =>
    padding.top + ((yMax - percent) / (yMax - yMin)) * (height - padding.top - padding.bottom);

  const line = [
    `M${x(start)},${y(baseline.percent)}`,
    ...points.map((point) => `H${x(point.time)} V${y(point.percent)}`),
    `H${x(end)}`,
  ].join(" ");

  return (
    <svg
      className={`bound-chart bound-chart-${variant} race-chart`}
      viewBox={`0 0 ${width} ${height}`}
      role="img"
      aria-label={`Kernel-verified records since ${dayLabel.format(start)}: from the ${truncateDecimalString(baseline.record.scorePercent, 3)}% Zeta23 baseline to ${truncateDecimalString(last.record.scorePercent, 3)}% across ${points.length} accepted records.`}
    >
      {yTicks.map((tick) => (
        <g key={tick}>
          <line x1={padding.left} y1={y(tick)} x2={width - padding.right} y2={y(tick)} className="chart-grid" />
          <text x={padding.left - 12} y={y(tick) + 4} textAnchor="end" className="chart-label">
            {percentLabel(tick, step)}
          </text>
        </g>
      ))}
      {shownXTicks.map((tick, index) => (
        <text
          key={tick}
          x={x(tick)}
          y={height - 14}
          textAnchor={index === 0 ? "start" : "middle"}
          className="chart-label"
        >
          {dayLabel.format(tick)}
        </text>
      ))}
      <path d={line} className="chart-line" />
      {/* Right of the first riser, where the plot is empty below the line. */}
      <text x={x(points[0].time) + 10} y={y(baseline.percent) + 4} className="chart-label">
        ← Zeta23 baseline {truncateDecimalString(baseline.record.scorePercent, 3)}%, {baseline.when}
      </text>
      {points.map((point, index) => {
        const isCurrent = index === points.length - 1;
        return (
          <g key={point.record.id}>
            <title>{`${point.when} · ${point.record.author} · ${truncateDecimalString(point.record.scorePercent, 4)}%`}</title>
            <circle cx={x(point.time)} cy={y(point.percent)} r={12} className="chart-hit" />
            <circle
              cx={x(point.time)}
              cy={y(point.percent)}
              r={isCurrent ? 7 : 4.5}
              className={isCurrent ? "chart-point chart-point-current" : "chart-point"}
            />
          </g>
        );
      })}
      <text x={x(last.time) - 12} y={y(last.percent) - 14} textAnchor="end" className="chart-value">
        {truncateDecimalString(last.record.scorePercent, 3)}%
      </text>
    </svg>
  );
}

const RACE_WIDE: Geometry = { ...WIDE, height: 280, padding: { top: 36, right: 34, bottom: 46, left: 72 } };
const RACE_COMPACT: Geometry = { ...COMPACT, height: 300, padding: { top: 40, right: 22, bottom: 48, left: 64 } };

function raceData(records: RecordEntry[]): { baseline: RacePoint; points: RacePoint[] } | null {
  const verified = records.filter((record) => record.status === "kernel-verified");
  const toPoint = (record: RecordEntry): RacePoint => {
    const verifiedAt = recordVerifiedAt(record);
    return {
      record,
      time: Date.parse(verifiedAt ?? `${record.date}T00:00:00Z`),
      percent: Number(record.scorePercent),
      when: formatRecordTime(record, verifiedAt),
    };
  };
  const [first, ...rest] = verified;
  const points = rest.map(toPoint);
  return first && points.length > 0 ? { baseline: toPoint(first), points } : null;
}

export function BoundChart({ records }: { records: RecordEntry[] }) {
  const race = raceData(records);
  // Plot one point per year: several records in the same year would otherwise
  // stack on one x position and overprint their labels. Records are ordered and
  // strictly increasing, so the last record of a year is that year's best.
  const byYear = new Map<number, ChartPoint>();
  for (const record of records) {
    const year = Number(record.date.slice(0, 4));
    byYear.set(year, {
      record,
      year,
      score: Number(record.scoreDecimal),
      recordsThatYear: (byYear.get(year)?.recordsThatYear ?? 0) + 1,
    });
  }
  const points = [...byYear.values()];

  return (
    <figure className="chart-card" aria-labelledby="history-title">
      <div className="section-heading chart-heading">
        <div>
          <span className="eyebrow">Record history</span>
          <h2 id="history-title">Published lower bounds since 1974</h2>
        </div>
        <span className="chart-unit">Certified lower bound</span>
      </div>
      <ChartSvg points={points} geometry={WIDE} variant="wide" />
      <ChartSvg points={points} geometry={COMPACT} variant="compact" />
      {race && (
        <>
          <div className="section-heading chart-heading race-heading">
            <div>
              <span className="eyebrow">Zoomed in</span>
              <h3>Kernel-verified records on riemann.fun</h3>
            </div>
            <span className="chart-unit">
              {race.points.length} records · +{(race.points.at(-1)!.percent - race.baseline.percent).toFixed(3)} percentage points
            </span>
          </div>
          <RaceChartSvg {...race} geometry={RACE_WIDE} variant="wide" />
          <RaceChartSvg {...race} geometry={RACE_COMPACT} variant="compact" />
        </>
      )}
      <figcaption className="sr-only">
        Historical published and formally verified unconditional lower bounds. All displayed values are truncated,
        never rounded up.
      </figcaption>
    </figure>
  );
}
