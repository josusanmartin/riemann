"use server";

import { signIn, signOut } from "@/auth";

export async function signInWithGitHub(): Promise<void> {
  await signIn("github", { redirectTo: "/submit" });
}

export async function signOutFromGitHub(): Promise<void> {
  await signOut({ redirectTo: "/" });
}
