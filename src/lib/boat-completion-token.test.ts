import { afterEach, expect, it, vi } from "vitest";
import {
  boatCompletionToken,
  validBoatCompletion,
} from "./boat-completion-token";
afterEach(() => vi.unstubAllEnvs());
it("binds a completion notification to one admitted job and proof digest", () => {
  vi.stubEnv("AUTH_SECRET", "test secret");
  const id = "12345678-1234-4123-8123-123456789abc",
    digest = "a".repeat(64);
  const token = boatCompletionToken(id, digest, "test secret");
  expect(validBoatCompletion(id, digest, token)).toBe(true);
  expect(validBoatCompletion(id, "b".repeat(64), token)).toBe(false);
  expect(validBoatCompletion(id.replace("abc", "abd"), digest, token)).toBe(
    false,
  );
  expect(validBoatCompletion(id, digest, "")).toBe(false);
});
