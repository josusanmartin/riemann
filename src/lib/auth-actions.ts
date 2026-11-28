"use server";

import { signIn, signOut } from "@/auth";

export async function signInWithGitHub(): Promise<void> {
  await signIn("github", { redirectTo: "/submit" });
}

export async function signInToAccountView(view: string): Promise<void> {
  const redirectTo = view === "admin" ? "/admin" : view === "dashboard" ? "/dashboard" : "/submit";
  await signIn("github", { redirectTo });
}

export async function signOutFromGitHub(): Promise<void> {
  await signOut({ redirectTo: "/" });
}
