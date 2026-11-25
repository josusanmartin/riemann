"use server";
import { getSession, signIn } from "@/auth";
import { approveCli, pairingPath, validPairing, type Pairing } from "@/lib/cli-login";

export async function signInForCli(input: Pairing) {
  const pairing = validPairing(input);
  if (!pairing) throw new Error("This login request expired. Run riemann login again.");
  await signIn("github", { redirectTo: pairingPath(pairing) });
}

export async function approveCliLogin(input: Pairing) {
  const pairing = validPairing(input);
  if (!pairing) return { error: "This login request expired. Start a new one in the CLI." };
  const session = await getSession();
  if (!session?.user.githubId || !session.user.githubLogin) return { error: "Refresh this page and sign in with GitHub." };
  return { approval: await approveCli(pairing, session.user) };
}
