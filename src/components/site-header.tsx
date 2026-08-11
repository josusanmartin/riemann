import Link from "next/link";
import { Github, LogOut } from "lucide-react";
import { getSession, isGitHubAuthConfigured } from "@/auth";
import { signInWithGitHub, signOutFromGitHub } from "@/lib/auth-actions";
import { BrandMark } from "@/components/brand-mark";
import { MobileMenu } from "@/components/mobile-menu";

const navigation = [
  { href: "/#leaderboard", label: "Leaderboard" },
  { href: "/challenge", label: "Challenge" },
  { href: "/methodology", label: "Verification" },
  { href: "/submit", label: "Submit" },
];

export async function SiteHeader() {
  const session = await getSession();

  return (
    <header className="site-header">
      <div className="shell header-inner">
        <Link className="brand" href="/" aria-label="Riemann.fail home">
          <BrandMark className="brand-mark" />
          <span>Riemann<span className="brand-dot">.fail</span></span>
        </Link>

        <nav className="desktop-nav" aria-label="Primary navigation">
          {navigation.map((item) => (
            <Link key={item.href} href={item.href}>
              {item.label}
            </Link>
          ))}
        </nav>

        <div className="header-auth">
          {session?.user ? (
            <>
              <span className="user-handle">
                @{session.user.githubLogin ?? session.user.name ?? "github"}
              </span>
              <form action={signOutFromGitHub}>
                <button className="icon-button" type="submit" aria-label="Sign out">
                  <LogOut size={16} />
                </button>
              </form>
            </>
          ) : isGitHubAuthConfigured ? (
            <form action={signInWithGitHub}>
              <button className="button button-small button-dark" type="submit">
                <Github size={16} />
                Sign in
              </button>
            </form>
          ) : (
            <Link className="button button-small button-dark" href="/signin">
              <Github size={16} />
              Sign in
            </Link>
          )}
        </div>

        <MobileMenu items={navigation} />
      </div>
    </header>
  );
}
