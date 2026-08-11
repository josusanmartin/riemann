import { Template, defaultBuildLogger } from "e2b";
import { createRiemannVerifierTemplate } from "./template";

const apiKey = process.env.E2B_API_KEY ?? process.env.E2B;
if (!apiKey) {
  throw new Error("Set E2B_API_KEY before building the verifier template");
}

const build = await Template.build(
  createRiemannVerifierTemplate(),
  "riemann-fail-verifier",
  {
    apiKey,
    cpuCount: 4,
    memoryMB: 8_192,
    onBuildLogs: defaultBuildLogger(),
  },
);

console.log(
  JSON.stringify(
    {
      name: build.name,
      templateId: build.templateId,
      buildId: build.buildId,
      tags: build.tags,
    },
    null,
    2,
  ),
);
