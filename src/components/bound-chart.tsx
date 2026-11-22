import type { RecordEntry } from "@/lib/challenge";
import { truncateDecimalString } from "@/components/format";
import { formatRecordTime, recordVerifiedAt } from "@/lib/record-times";

const DAY = 86_400_000;
const dateLabel = new Intl.DateTimeFormat("en-US", {
  month: "short",
  day: "numeric",
  timeZone: "UTC",
});
const timeLabel = new Intl.DateTimeFormat("en-GB", {
  hour: "2-digit",
  minute: "2-digit",
  timeZone: "UTC",
});

function chartPoint(record: RecordEntry) {
  const verifiedAt = recordVerifiedAt(record);
  return {
    record,
    time: Date.parse(verifiedAt ?? `${record.date}T00:00:00Z`),
    value: Number(record.scorePercent),
    date: formatRecordTime(record, verifiedAt),
  };
}

type Point = ReturnType<typeof chartPoint>;
const percent = (p: Point, digits = 3) =>
  `${truncateDecimalString(p.record.scorePercent, digits)}%`;

function History({
  points,
  firstRH,
  compact,
}: {
  points: Point[];
  firstRH?: Point;
  compact: boolean;
}) {
  const width = compact ? 380 : 800,
    height = compact ? 240 : 250;
  const left = compact ? 38 : 46,
    right = width - (compact ? 24 : 36),
    bottom = height - 40;
  const max = Math.max(
    70,
    Math.ceil(Math.max(...points.map((p) => p.value)) / 10) * 10,
  );
  const y = (v: number) => bottom - ((v - 30) / (max - 30)) * (bottom - 28);
  const x = (i: number) =>
    left + ((right - left) * i) / Math.max(points.length - 1, 1);
  const change = firstRH ? points.indexOf(firstRH) : -1;
  return (
    <svg
      className={`bound-chart bound-chart-${compact ? "compact" : "wide"}`}
      viewBox={`0 0 ${width} ${height}`}
      role="img"
      aria-label={`Selected milestones in chronological order. ${points.map((p) => `${p.date}, ${percent(p)}${p === firstRH ? ", first record using the published RH proof" : ""}`).join(". ")}`}
    >
      {Array.from({ length: (max - 30) / 10 + 1 }, (_, i) => 30 + 10 * i).map(
        (v) => (
          <g key={v}>
            <line
              className="chart-grid"
              x1={left}
              x2={right}
              y1={y(v)}
              y2={y(v)}
            />
            <text
              className="chart-label"
              x={left - 7}
              y={y(v) + 4}
              textAnchor="end"
            >
              {v}%
            </text>
          </g>
        ),
      )}
      {points.map(
        (p, i) =>
          i > 0 && (
            <g key={p.record.id}>
              <path
                className="chart-line"
                d={`M${x(i - 1)} ${y(points[i - 1].value)} H${x(i)}`}
              />
              <path
                className={i === change ? "chart-line rh-step" : "chart-line"}
                d={`M${x(i)} ${y(points[i - 1].value)} V${y(p.value)}`}
              />
            </g>
          ),
      )}
      {points.map((p, i) => {
        const last = i === points.length - 1;
        const anchor = i === 0 ? "start" : last ? "end" : "middle";
        const label =
          p.record.status === "published"
            ? p.record.date.slice(0, 4)
            : dateLabel.format(p.time);
        return (
          <g key={p.record.id}>
            <title>{`${p.date} · ${p.record.author} · ${percent(p, 5)}`}</title>
            <circle
              className={`chart-point${last ? " chart-point-current" : ""}`}
              cx={x(i)}
              cy={y(p.value)}
              r={last ? 5.5 : 3.8}
            />
            {(!compact || (i !== change && i !== change - 1) || last) && (
              <text
                className="chart-value"
                textAnchor={anchor}
                x={x(i)}
                y={y(p.value) - (i === change && !last ? 11 : 13)}
              >
                {percent(p, p.record.status === "published" ? 1 : 2)}
              </text>
            )}
            <text
              className="chart-label history-date"
              textAnchor={compact && last ? "middle" : anchor}
              x={x(i)}
              y={bottom + 21}
            >
              {compact && change >= 0 && i === change - 1
                ? ""
                : compact && i === change
                  ? "RH"
                  : compact && last
                    ? "Latest"
                    : label}
            </text>
          </g>
        );
      })}
    </svg>
  );
}

function Detail({
  points,
  start,
  title,
  count,
}: {
  points: Point[];
  start: number;
  title: string;
  count: number;
}) {
  const first = points[0],
    last = points[points.length - 1];
  const end = Math.max(last.time, start + 60_000);
  const span = Math.max(last.value - first.value, 0.001);
  const power = 10 ** Math.floor(Math.log10(span / 3));
  const step = ([1, 2, 5, 10].find((n) => n * power >= span / 3) ?? 10) * power;
  const low = Math.floor(first.value / step) * step,
    high = Math.max(low + step, Math.ceil(last.value / step) * step);
  const left = 58,
    right = 373,
    bottom = 124;
  const x = (t: number) =>
    left + ((Math.max(start, t) - start) / (end - start)) * (right - left);
  const y = (v: number) => bottom - ((v - low) / (high - low)) * 98;
  const line = points
    .map((p, i) =>
      i ? `H${x(p.time)} V${y(p.value)}` : `M${left} ${y(p.value)}`,
    )
    .join(" ");
  const sameDay = Math.floor(start / DAY) === Math.floor(end / DAY);
  const tickLabel = sameDay ? timeLabel : dateLabel;
  const ticks =
    end - start >= 5 * DAY ? [start, (start + end) / 2, end] : [start, end];
  return (
    <section className="record-period">
      <h4>{title}</h4>
      <p className="period-range">
        {percent(first)} <span aria-label="to">→</span>{" "}
        <strong>{percent(last)}</strong>
      </p>
      <p className="period-count">
        {count} {count === 1 ? "record" : "records"} ·{" "}
        {sameDay ? dateLabel.format(start) + ", " : ""}
        {new Date(start).getUTCFullYear()}
      </p>
      <svg
        viewBox="0 0 394 156"
        role="img"
        aria-label={`${title}. ${count} verified records, ${percent(first)} to ${percent(last)}. Dates in UTC.`}
      >
        {Array.from(
          { length: Math.round((high - low) / step) + 1 },
          (_, i) => low + i * step,
        ).map((v) => (
          <g key={v}>
            <line
              className="chart-grid"
              x1={left}
              x2={right}
              y1={y(v)}
              y2={y(v)}
            />
            <text
              className="chart-label"
              x={left - 6}
              y={y(v) + 4}
              textAnchor="end"
            >
              {v.toFixed(Math.max(0, -Math.floor(Math.log10(step) + 1e-9)))}%
            </text>
          </g>
        ))}
        <path className="chart-line" d={line} />
        {points.map((p, i) => (
          <circle
            key={p.record.id}
            cx={i === 0 ? left : x(p.time)}
            cy={y(p.value)}
            r={i === points.length - 1 ? 4.5 : 2.2}
            className={
              i === points.length - 1
                ? "chart-point chart-point-current"
                : "chart-point"
            }
          >
            <title>{`${p.date} · ${p.record.author} · ${percent(p, 6)}`}</title>
          </circle>
        ))}
        {ticks.map((t, i) => (
          <text
            key={t}
            className="chart-label"
            x={x(t)}
            y={bottom + 21}
            textAnchor={
              i === 0 ? "start" : i === ticks.length - 1 ? "end" : "middle"
            }
          >
            {tickLabel.format(t)}
          </text>
        ))}
      </svg>
    </section>
  );
}

export function BoundChart({ records }: { records: RecordEntry[] }) {
  const all = records.map(chartPoint);
  const verified = all.filter((p) => p.record.status === "kernel-verified");
  const before = verified.filter((p) => !p.record.rhFoundationCommit);
  const after = verified.filter((p) => p.record.rhFoundationCommit);
  const firstRH = after[0],
    pre = before.at(-1),
    current = verified.at(-1);
  const milestones = all.filter(
    (p) =>
      p.record.status === "published" ||
      p === before[0] ||
      p === pre ||
      p === firstRH ||
      p === current,
  );
  const raceStart = before[1]?.time ?? before[0]?.time;
  return (
    <figure className="chart-card" aria-labelledby="history-title">
      <div className="section-heading chart-heading">
        <div>
          <span className="eyebrow">Record history</span>
          <h2 id="history-title">Critical-line bounds since 1974</h2>
          <p className="chart-note">
            Selected milestones, spaced by event. Dates in UTC.
          </p>
        </div>
      </div>
      <History points={milestones} firstRH={firstRH} compact={false} />
      <History points={milestones} firstRH={firstRH} compact />
      {firstRH && pre && (
        <p className="rh-jump-note">
          <span className="rh-line-key" aria-hidden="true" />
          <span>
            <strong>RH announcement · Nov 20, 2026.</strong> On{" "}
            {dateLabel.format(firstRH.time)}, the first record using Alpöge’s
            published proof raised the bound from {percent(pre)} to{" "}
            <a href={`/submissions/${firstRH.record.id}`}>{percent(firstRH)}</a>
            . <a href="https://math.mit.edu/~drew/grh/">Proof announcement</a>
          </span>
        </p>
      )}
      {verified.length > 1 && current && (
        <div className="record-detail">
          <div className="section-heading chart-heading">
            <div>
              <h3>Kernel-verified records</h3>
              <p className="chart-note">
                Each period has its own percentage scale so smaller gains remain
                visible.
              </p>
            </div>
          </div>
          <div className="record-periods">
            {before.length > 0 && raceStart !== undefined && (
              <Detail
                title="Before the RH premise"
                points={before}
                start={Math.floor(raceStart / DAY) * DAY}
                count={Math.max(0, before.length - 1)}
              />
            )}
            {firstRH && (
              <Detail
                title="With the published RH premise"
                points={after}
                start={firstRH.time}
                count={after.length}
              />
            )}
          </div>
          {before[0] && (
            <p className="chart-note record-baseline">
              Zeta23 baseline · {percent(before[0])} on {before[0].date}. The
              subsequent {verified.length - 1} records gained about{" "}
              {(current.value - before[0].value).toFixed(3)} percentage points.
            </p>
          )}
        </div>
      )}
    </figure>
  );
}
