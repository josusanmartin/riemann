import { ImageResponse } from "next/og";
import { getCurrentRecord } from "@/lib/records";
import { truncateDecimalString } from "@/components/format";

export const alt = "Riemann zeta function critical-line bound record";
export const size = { width: 1200, height: 630 };
export const contentType = "image/png";

export default function OpenGraphImage(): ImageResponse {
  const current = getCurrentRecord();
  const percent = truncateDecimalString(current.scorePercent, 10);

  return new ImageResponse(
    (
      <div
        style={{
          width: "100%",
          height: "100%",
          display: "flex",
          position: "relative",
          overflow: "hidden",
          padding: "68px 76px",
          background: "#0b211c",
          color: "#fffefa",
          fontFamily: "Arial, sans-serif",
        }}
      >
        <div
          style={{
            position: "absolute",
            width: 720,
            height: 720,
            top: -360,
            right: -100,
            borderRadius: 9999,
            background: "rgba(33, 107, 88, 0.42)",
          }}
        />
        <div
          style={{
            display: "flex",
            width: "100%",
            flexDirection: "column",
            justifyContent: "space-between",
          }}
        >
          <div style={{ display: "flex", alignItems: "center", gap: 18 }}>
            <div
              style={{
                width: 58,
                height: 58,
                display: "flex",
                alignItems: "center",
                justifyContent: "center",
                borderRadius: 17,
                background: "#d8f58b",
                color: "#142d27",
                fontSize: 35,
                fontWeight: 700,
              }}
            >
              Σ
            </div>
            <div style={{ display: "flex", fontSize: 32, fontWeight: 700 }}>
              Riemann<span style={{ color: "#9fb0aa", fontWeight: 500 }}>&nbsp;zeta function</span>
            </div>
          </div>

          <div style={{ display: "flex", alignItems: "flex-end", justifyContent: "space-between" }}>
            <div style={{ display: "flex", maxWidth: 620, flexDirection: "column" }}>
              <div style={{ marginBottom: 18, color: "#d8f58b", fontSize: 20, letterSpacing: 3 }}>
                UNCONDITIONAL CRITICAL-LINE BOUND
              </div>
              <div style={{ fontSize: 60, lineHeight: 1.04, letterSpacing: -2 }}>
                The largest proven proportion of zeros on the critical line.
              </div>
            </div>
            <div style={{ display: "flex", flexDirection: "column", alignItems: "flex-end" }}>
              <div style={{ color: "#9fb0aa", fontSize: 18 }}>Current verified record</div>
              <div style={{ display: "flex", color: "#d8f58b", fontSize: 54, fontWeight: 700 }}>
                {percent}%
              </div>
            </div>
          </div>
        </div>
      </div>
    ),
    size,
  );
}
