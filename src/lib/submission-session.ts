import { getSession } from "@/auth";
import { cliBearerPrefix, cliSession } from "./cli-login";

// Only the competitive submission endpoints and CLI identity check opt in.
export async function getSubmissionSession(request: Request) {
  const authorization = request.headers.get("authorization");
  if (authorization?.startsWith(cliBearerPrefix)) return cliSession(authorization);
  return getSession(request);
}
