import { redirect } from "next/navigation";

export default async function History({ searchParams }: { searchParams: Promise<{ attempt?: string }> }) {
  const { attempt } = await searchParams;
  redirect(typeof attempt === "string" ? `/dashboard?attempt=${encodeURIComponent(attempt)}#attempt` : "/dashboard");
}
