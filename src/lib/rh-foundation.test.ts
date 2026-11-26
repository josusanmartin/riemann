import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { contract } from "./records";

describe("published RH foundation", () => {
  it("binds the exact release manifest to the compiler and Mathlib pins", () => {
    const pins = contract.trustedUpstream;
    const manifest = readFileSync("challenge/foundation/lake-manifest.json");
    expect(createHash("sha256").update(manifest).digest("hex")).toBe(pins.rh.dependencyManifestSha256);
    expect(JSON.parse(manifest.toString()).packages).toContainEqual(expect.objectContaining({
      name: "mathlib", rev: pins.mathlibCommit,
    }));
    expect(readFileSync("challenge/smoke/lean-toolchain","utf8").trim()).toBe(pins.leanToolchain);
  });

  it("exposes the published theorem through the same trusted reference as the candidate", () => {
    const { interfaceAxiom, releaseTheorem } = contract.trustedUpstream.rh;
    const source = readFileSync("challenge/templates/Main.lean","utf8");
    expect(source.match(/^axiom .*$/gm)).toEqual([`axiom ${interfaceAxiom} : RiemannHypothesis`]);
    expect(source).toContain(`theorem ${releaseTheorem} : RiemannHypothesis := ${interfaceAxiom}`);
    expect(contract.permittedAxioms).toEqual(["propext","Quot.sound","Classical.choice"]);
    expect(readFileSync("boat/compact/Main.lean","utf8")).toContain("New.zeta_zeros_on_line New.grh");
    expect(readFileSync("challenge/templates/CandidateSpec.lean.tmpl","utf8")).toContain("import Main\n");
  });
});
