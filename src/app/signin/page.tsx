import type { Metadata } from "next";
import Link from "next/link";
import { ArrowLeft, Github, KeyRound, ShieldCheck } from "lucide-react";
import { getSession, isGitHubAuthConfigured } from "@/auth";
import { BrandMark } from "@/components/brand-mark";
import { signInWithGitHub, signOutFromGitHub } from "@/lib/auth-actions";
import { repositoryUrl } from "@/lib/site";

export const metadata: Metadata = { title: "Sign in" };

function describeAuthError(code: string): string {
  switch (code) {
    case "AccessDenied":
      return "GitHub reported that access was denied. Nothing was stored; you can retry whenever you are ready.";
    case "Configuration":
      return "Sign-in is misconfigured on this deployment. The public pull-request workflow still works in the meantime.";
    case "Verification":
      return "That sign-in link expired or was already used. Please start again from this page.";
    default:
      return "GitHub sign-in did not complete. Nothing was saved. Please try again.";
  }
}

export default async function SignInPage({
  searchParams,
}: {
  searchParams: Promise<{ error?: string }>;
}) {
  const session = await getSession();
  const { error } = await searchParams;
  const errorMessage = error ? describeAuthError(error) : null;

  return (
    <main id="main-content" className="signin-page">
      <section className="signin-card">
        <BrandMark className="signin-mark" />
        <span className="eyebrow">Contributor identity</span>
        <h1>{session?.user ? "You are signed in." : "Sign in with GitHub"}</h1>
        {errorMessage && <p className="signin-error" role="alert">{errorMessage}</p>}
        {session?.user ? (
          <>
            <p>Authenticated as <strong>@{session.user.githubLogin ?? session.user.name}</strong>. You can now upload a formal entry directly to the isolated verifier.</p>
            <div className="signin-actions">
              <Link className="button button-lime" href="/submit">Continue to submit</Link>
              <form action={signOutFromGitHub}><button className="button button-ghost-light" type="submit">Sign out</button></form>
            </div>
          </>
        ) : isGitHubAuthConfigured ? (
          <>
            <p>Sign in with GitHub to prepare a submission. The site requests read-only access to your public profile and email.</p>
            <form action={signInWithGitHub}>
              <button className="button button-lime signin-button" type="submit"><Github size={18} /> Continue with GitHub</button>
            </form>
          </>
        ) : (
          <>
            <p>GitHub sign-in has not been enabled for this deployment yet. The challenge remains open through the public repository.</p>
            <a className="button button-lime signin-button" href={repositoryUrl} target="_blank" rel="noreferrer"><Github size={18} /> Open GitHub repository</a>
          </>
        )}
        <div className="signin-security">
          <span><KeyRound size={15} /> No password stored</span>
          <span><ShieldCheck size={15} /> No repository write access</span>
        </div>
        <Link className="back-link" href="/"><ArrowLeft size={15} /> Return to the leaderboard</Link>
      </section>
    </main>
  );
}
