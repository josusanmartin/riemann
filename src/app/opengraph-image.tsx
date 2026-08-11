import { ImageResponse } from "next/og";
import { getCurrentRecord } from "@/lib/records";
import { truncateDecimalString } from "@/components/format";

export const alt = "Riemann.fail critical-line formal proof challenge";
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
            <div style={{ display: "flex", fontSize: 34, fontWeight: 700 }}>
              Riemann<span style={{ color: "#ff7557" }}>.fail</span>
            </div>
          </div>

          <div style={{ display: "flex", alignItems: "flex-end", justifyContent: "space-between" }}>
            <div style={{ display: "flex", maxWidth: 620, flexDirection: "column" }}>
              <div style={{ marginBottom: 18, color: "#d8f58b", fontSize: 20, letterSpacing: 3 }}>
                OPEN FORMAL CHALLENGE
              </div>
              <div style={{ fontSize: 66, lineHeight: 1.02, letterSpacing: -3 }}>
                The bound only moves when the proof checks.
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
