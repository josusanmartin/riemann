import Link from "next/link";
import { getSession } from "@/auth";
import { validPairing } from "@/lib/cli-login";
import { signInForCli } from "./actions";
import { Approval } from "./approval";

export const dynamic = "force-dynamic";
export const metadata = { title: "CLI login", robots: { index: false, follow: false } };

export default async function CliLoginPage({ searchParams }: { searchParams: Promise<Record<string, string | string[] | undefined>> }) {
  const pairing = validPairing(await searchParams);
  const user = pairing ? (await getSession())?.user : null;
  return <main id="main-content" className="signin-page"><section className="signin-card">
    <h1>CLI login</h1>
    {pairing ? <>
      <p>Match this code to the one in the terminal where you started login.</p>
      <p><strong><code>{pairing.challenge.slice(0, 8)}</code></strong></p>
      <p>This CLI can submit competitive proofs and read your own run status and logs for 24 hours.</p>
      {user?.githubId && user.githubLogin ? <>
        <p>Approving as <strong>@{user.githubLogin}</strong>.</p>
        <Approval pairing={pairing} />
      </> : <form action={signInForCli.bind(null, pairing)}><button className="button button-lime" type="submit">Sign in with GitHub</button></form>}
    </> : <p>Run <code>riemann login</code> in your terminal to start a fresh login request.</p>}
    <Link className="back-link" href="/submit/agent">CLI guide</Link>
  </section></main>;
}
