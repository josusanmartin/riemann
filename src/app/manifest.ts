import type { MetadataRoute } from "next";

export default function manifest(): MetadataRoute.Manifest {
  return {
    name: "Riemann.fail",
    short_name: "Riemann.fail",
    description:
      "A machine-checked frontier for unconditional critical-line bounds.",
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
