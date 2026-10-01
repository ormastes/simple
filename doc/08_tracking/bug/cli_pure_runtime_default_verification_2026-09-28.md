# CLI pure runtime default: implementation and verification blocker

Status: source change implemented; runtime verification blocked, not PASS.

Base: `origin/main` at `0dbb2c1691a`; isolated worktree
`/tmp/simple-cli-pure-runtime-default`. No commit, push, deployment, or Rust
seed execution was performed.

## Policy and scope

AGENTS.md requires ordinary tooling to execute on the pure-Simple runtime.
`app.io.cli_ops._cli_driver_binary` previously selected an installed sibling
`simple_seed`, then a cwd-relative seed or wrapper automatically.
`_cli_frontend_delegate_binary` independently repeated the sibling fallback.
The change removes both automatic selections. An empty selection invokes the
existing in-process implementation. Explicit `SIMPLE_BOOTSTRAP_DRIVER` and
`SIMPLE_FRONTEND_DELEGATE` retain the existing bootstrap entrypoint contracts;
self-exec checks and frontend loop suppression remain. The exact
`SIMPLE_NO_BOOTSTRAP_DELEGATE=1` admission flag now suppresses both selectors.
The release-runtime repository-wrapper guard also applies to explicit driver
selection. Cached production MCP/LSP wrappers are untouched.

The regression spec covers default in-process selections, explicit bootstrap
selection, admission suppression, explicit frontend selection, frontend loop
prevention, and self-exec rejection. The pre-existing Windows identity bypass
is unchanged; this patch does not establish Windows self-exec evidence.

## Verification attempted once

Runtime: `/Users/ormastes/simple/bin/release/aarch64-apple-darwin/simple`
SHA-256: `f2c216a660da83da1a253d2e8191a3059a66b1d9dc11bbcbaf237fe7e5b8d2bc`.
This is the installed pure-Simple release artifact, not a rebuild of this patch.
Source imports were directed to the isolated checkout:

```sh
env -u SIMPLE_BOOTSTRAP_DRIVER -u SIMPLE_FRONTEND_DELEGATE \
  SIMPLE_NO_BOOTSTRAP_DELEGATE=1 SIMPLE_FRONTEND_DELEGATED=1 \
  SIMPLE_LIB=/tmp/simple-cli-pure-runtime-default/src \
  /Users/ormastes/simple/bin/release/aarch64-apple-darwin/simple \
  test test/01_unit/app/io/cli_driver_no_bootstrap_delegate_spec.spl --mode=interpreter
```

Exit 1, 0 passed, 1 failed; failure before spec assertions:

```text
error: compile failed: parse: in "/private/tmp/simple-cli-pure-runtime-default/src/lib/nogc_sync_mut/io/process_ops.spl": Unexpected token: expected expression, found Colon
```

The dependency contains value-producing `unsafe(capabilities: [ffi]):`
initializers beginning at line 144; the runtime reports no exact line.
No unsupported grammar was rewritten as a workaround. A source-compatible
pure-Simple runtime is needed before these assertions or source-native CLI
integration can be accepted. `git diff --check` passed. No coverage, bootstrap
admission, runtime smoke, or release readiness claim is made.
