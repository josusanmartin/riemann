import type { RecordEntry } from "@/lib/challenge";
import { truncateDecimalString } from "@/components/format";

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

type ChartPoint = { record: RecordEntry; year: number; score: number };

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
            <title>{`${year} · ${record.author} · ${pointLabel(point, isCurrent)} · ${record.method}`}</title>
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

export function BoundChart({ records }: { records: RecordEntry[] }) {
  const points = records.map((record) => ({
    record,
    year: Number(record.date.slice(0, 4)),
    score: Number(record.scoreDecimal),
  }));

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
      <figcaption className="sr-only">
        Historical published and formally verified unconditional lower bounds. All displayed values are truncated,
        never rounded up.
      </figcaption>
    </figure>
  );
}
