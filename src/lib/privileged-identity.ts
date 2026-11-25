// Public immutable ID of the repository owner's GitHub account.
const repositoryOwner = { login: "josusanmartin", id: "5554649" };

export function isPrivilegedIdentity(login: string | undefined, githubId: string | undefined, allowed: string) {
  if (!login || !githubId || !/^[1-9][0-9]*$/.test(githubId)) return false;
  return allowed.split(",").some(raw => {
    const entry = raw.trim().toLowerCase();
    if (entry === repositoryOwner.login) return login.toLowerCase() === entry && githubId === repositoryOwner.id;
    return entry === `${login.toLowerCase()}:${githubId}`;
  });
}
