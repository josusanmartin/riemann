# Riemann submission CLI

The website distributes [riemann.mjs](./riemann.mjs) directly from this repository. The script includes the [MIT license](../../LICENSE) and runs on Node.js 22 or later without npm packages.

The [CLI guide](https://www.riemannzeta.fun/submit/agent) links to the exact source revision for the deployed download and displays its SHA-256 checksum. From a checkout of that revision, compare the download against the tracked file:

```sh
curl -fsSL https://www.riemannzeta.fun/cli/riemann.mjs | cmp public/cli/riemann.mjs -
```

Start a website login with `node public/cli/riemann.mjs login`. For headless login, submission metadata, polling, and exit codes, see the [agent instructions](https://www.riemannzeta.fun/agent-guide.md).

The CLI tests are in [scripts/agent-cli.test.ts](../../scripts/agent-cli.test.ts). Browser approval and credential validation are implemented in [src/app/cli/login](../../src/app/cli/login) and [src/lib/cli-login.ts](../../src/lib/cli-login.ts).
