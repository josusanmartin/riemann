export const repository =
  process.env.NEXT_PUBLIC_GITHUB_REPOSITORY ?? "josusanmartin/riemann";

export const repositoryUrl = `https://github.com/${repository}`;
export const newSubmissionUrl = `${repositoryUrl}/compare`;
export const siteUrl =
  process.env.NEXT_PUBLIC_SITE_URL?.replace(/\/$/, "") ?? "http://localhost:3000";
