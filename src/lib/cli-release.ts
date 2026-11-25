import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { repositoryUrl } from "./site";

const sha = process.env.RIEMANN_BASE_COMMIT_SHA ?? process.env.VERCEL_GIT_COMMIT_SHA;
const ref = sha && /^[a-f0-9]{40}$/.test(sha) ? sha : "main";
export const cliSource = `${repositoryUrl}/blob/${ref}/public/cli/riemann.mjs`;
export const cliLicense = `${repositoryUrl}/blob/${ref}/LICENSE`;
export const cliSha256 = createHash("sha256").update(readFileSync(join(process.cwd(), "public/cli/riemann.mjs"))).digest("hex");
