import type { MetadataRoute } from "next";
import { siteUrl } from "@/lib/site";
import { records } from "@/lib/records";

export default function sitemap(): MetadataRoute.Sitemap {
  const routes = ["", "/challenge", "/methodology", "/submit", "/submissions", ...records.map((record) => `/submissions/${record.id}`)];
  return routes.map((route) => ({ url: `${siteUrl}${route}`, changeFrequency: route === "" ? "daily" : "weekly", priority: route === "" ? 1 : 0.7 }));
}
