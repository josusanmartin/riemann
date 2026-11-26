import pins from "../../challenge/compact-runtime.json";

export function compactRuntimePinned(): boolean {
  return /^compact-runtime-build-[a-zA-Z0-9.-]+$/.test(pins.release) &&
    pins.parts.length > 0 && pins.parts.length <= 12 &&
    pins.parts.every((digest: string) => /^[0-9a-f]{64}$/.test(digest));
}
