import type { MetadataRoute } from "next";

export default function manifest(): MetadataRoute.Manifest {
  return {
    name: "Riemann zeta function",
    short_name: "Riemann ζ",
    description:
      "A machine-checked record of unconditional critical-line bounds for the Riemann zeta function.",
    start_url: "/",
    display: "standalone",
    background_color: "#f5f3eb",
    theme_color: "#0b211c",
    icons: [
      {
        src: "/icon.svg",
        sizes: "any",
        type: "image/svg+xml",
      },
    ],
  };
}
