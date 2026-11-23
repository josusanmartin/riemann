import { ImageResponse } from "next/og";
import { getRecord } from "@/lib/records";
import { recordPresentation } from "../presentation";

export async function GET(
  _request: Request,
  { params }: { params: Promise<{ id: string }> },
) {
  const record = getRecord((await params).id);
  if (!record) return new Response(null, { status: 404 });
  const { score, status, heading } = recordPresentation(record);
  return new ImageResponse(
    (
      <div
        style={{
          width: "100%",
          height: "100%",
          display: "flex",
          flexDirection: "column",
          justifyContent: "space-between",
          background: "#0b211c",
          color: "#fffefa",
          padding: "50px 68px",
          fontFamily: "sans-serif",
        }}
      >
        <div
          style={{
            display: "flex",
            justifyContent: "space-between",
            alignItems: "center",
            fontSize: 29,
          }}
        >
          <strong>Riemann zeta function</strong>
          <span style={{ color: "#d8f58b", fontSize: 24 }}>{status}</span>
        </div>
        <div style={{ display: "flex", flexDirection: "column" }}>
          <strong
            style={{
              color: "#d8f58b",
              fontSize: 152,
              letterSpacing: -8,
              lineHeight: 1.06,
            }}
          >
            {score}
          </strong>
          <span style={{ fontSize: 50, letterSpacing: -1 }}>{heading}</span>
          {record.rhFoundationCommit && (
            <span style={{ marginTop: 12, fontSize: 25, color: "#b9c9c2" }}>
              Under the published RH premise
            </span>
          )}
        </div>
        <div
          style={{
            display: "flex",
            justifyContent: "space-between",
            alignItems: "center",
            gap: 24,
            borderTop: "2px solid #35534a",
            paddingTop: 21,
            fontSize: 30,
          }}
        >
          <span>{record.author}</span>
          <span style={{ color: "#b9c9c2", fontSize: 25 }}>{record.date}</span>
        </div>
      </div>
    ),
    { width: 1200, height: 630 },
  );
}
