import NextAuth from "next-auth";
import GitHub from "next-auth/providers/github";
import type { DefaultSession, Session } from "next-auth";
import { siteUrl } from "@/lib/site";

declare module "next-auth" {
  interface Session {
    user: {
      githubLogin?: string;
    } & DefaultSession["user"];
  }
}

declare module "@auth/core/jwt" {
  interface JWT {
    githubLogin?: string;
  }
}

export const isGitHubAuthConfigured = Boolean(
  process.env.AUTH_GITHUB_ID &&
    process.env.AUTH_GITHUB_SECRET &&
    process.env.AUTH_SECRET,
);

const providers = isGitHubAuthConfigured
  ? [
      GitHub({
        clientId: process.env.AUTH_GITHUB_ID,
        clientSecret: process.env.AUTH_GITHUB_SECRET,
        authorization: { params: { scope: "read:user user:email" } },
      }),
    ]
  : [];

export const { handlers, auth, signIn, signOut } = NextAuth({
  providers,
  trustHost: true,
  redirectProxyUrl: siteUrl.startsWith("https://")
    ? `${siteUrl}/api/auth`
    : undefined,
  session: { strategy: "jwt" },
  callbacks: {
    jwt({ token, profile }) {
      if (profile && "login" in profile && typeof profile.login === "string") {
        token.githubLogin = profile.login;
      }
      return token;
    },
    session({ session, token }) {
      if (token.githubLogin) {
        session.user.githubLogin = token.githubLogin;
      }
      return session;
    },
  },
  pages: { signIn: "/signin", error: "/signin" },
});

export async function getSession(): Promise<Session | null> {
  if (!isGitHubAuthConfigured) return null;
  return auth();
}
