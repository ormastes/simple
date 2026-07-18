# Pure Simple Tooling Contract

This guide records the production contract for `bin/simple` tooling.

## Runtime Boundary

`test`, `test-daemon`, `check`, `examples-check`, `fmt`, `lint`, `fix`, `duplicate-check`,
`verify`, `spipe-docgen`, `native-build`, `vscode`, `electron`, and `security`
must route to pure Simple entrypoints by default. The Rust compiler under
`src/compiler_rust/` is a seed/bootstrap implementation only. It must not be
used as a fallback for migrated public tools.

Rust-built seed tools must print a `WARNING` that they are bootstrap-only and
that users should build/use the pure-Simple `bin/simple` instead. Bootstrap
internals may suppress that warning with `SIMPLE_BOOTSTRAP=1`; normal users
should see it when they run `src/compiler_rust/target/bootstrap/simple`.

When a migrated tool is slow, flaky, or resource-heavy, fix the pure Simple
implementation in `src/compiler`, `src/lib`, or `src/app`, or record a concrete
bug. Do not re-enable a Rust escape hatch.

`spipe-docgen` must run through a pure-Simple `simple-core` or
`core-c-bootstrap` runtime. Treat unresolved runtime symbols, nonzero or signal
exits, and missing generated output as runtime defects. Fix the owning runtime
provider and rerun docgen; do not accept a hand-edited manual or Rust-seed
output as generated evidence.

## Bootstrap Build Modes

`scripts/bootstrap/bootstrap-from-scratch.sh` is pure-Simple-only by default and
does not rebuild Rust. Use `--full-bootstrap` for the rare Rust seed/runtime
rebuild.

Pure-Simple rebuilds use two mode names:

- `dynload` (default): faster iteration; keep reusable per-module native/SMF
  cache entries, rebuild changed pure-Simple modules, and skip the full CLI
  relink.
- `one-binary`: conservative monolithic native executable; clear the native
  cache before stages.

Native-build cache artifacts default to `build/native_cache`. Bootstrap
overrides that to `build/bootstrap/native_cache` so staged compiler artifacts
stay under the bootstrap build tree. Use bootstrap `--fresh-cache` when you
want a clean dynload cache without rebuilding the Rust seed/runtime; use
`--full-bootstrap` only when Rust seed/runtime inputs must be rebuilt.

Use `--full-cli` when a new monolithic CLI is required, `--deploy` to build and
install it, and `--full-bootstrap` only when Rust seed/runtime inputs changed.
`--mode=one-binary` also implies a full CLI relink.

Dependency tracing remains conservative around AOP/MDSOC weaving. The native
cache fingerprints module sources, while the wrapper broadly invalidates on
platform/backend/mode and AOP/MDSOC/weaving/loader environment changes. Use
`--fresh-cache` after compiler code-generation semantic or dependency-interface
changes that are wider than a leaf source-body edit.

## Test Runner Daemon

`bin/simple test <spec>` is client-driven but daemon-owned: the client may
auto-start the test daemon, then the daemon owns test execution so interpreter,
compiler, and runner resource use remain centrally controlled.

The client must detect stale or dead daemon state, replace the stale lock/PID,
and keep `test-daemon start/status/stop` available through pure Simple
entrypoints. A stale daemon lock must not force users to clean files manually.

## Resource Guard

Tooling must avoid default-output floods, unbounded child process output,
repeated green-check loops, and orphan daemon/test process buildup. Diagnostic
compiler/linker traces belong behind `SIMPLE_COMPILER_TRACE=1` or another
explicit debug flag.

Verification for tooling changes should include:

- stale/dead test-daemon recovery evidence;
- command dispatch coverage for migrated tools;
- Rust fallback audit showing zero migrated-tool escape hatches;
- direct env/process facade guard;
- bounded-output smoke for performance-sensitive tools such as `native-build`.

The production test runner uses `process_run_bounded` (and the bounded limits
variant) with a 4 MiB cap for each stdout/stderr stream. Truncated streams keep
their head and tail and include an exact omitted-byte marker, so early compiler
diagnostics and final SPipe summaries remain available. Parallel temp-file and
fork capture apply the same bound. Timeout handling must kill the process group
where supported and must never block indefinitely waiting for a descendant that
kept a pipe open. A plain `-1` exit is not sufficient timeout evidence; require
the timeout marker so spawn/internal failures remain ordinary failures.
Pure-Simple callers use the `std.io` facade; hosted C owns the OS capture and
cleanup boundary, and native LLVM calls cross the dedicated tuple ABI facade.

For staged compiler or MCP changes, the bootstrap wrapper must pass its built-in
Stage 2 and Stage 3 compiler sanity, then run the matching stage sanity SSpec
and MCP command-line handshake SSpec. `bin/simple_mcp_server` defaults to the cached
native server; `SIMPLE_MCP_NATIVE` selects an exact artifact for reproducible
verification. Raw-source execution is an explicit debug fallback controlled by
`SIMPLE_MCP_ALLOW_SOURCE_FALLBACK=1` and may use only a deployed pure-Simple
runtime. A wrapper handshake that silently runs raw source or the Rust seed is
not production evidence.

Every bootstrap route that produces a Stage 4 full CLI runs
`scripts/check/check-bootstrap-essential-tools-smoke.shs` with the exact fresh
binary. From a temporary non-repository working directory it checks real
test-runner pass/fail/empty outcomes, focused lint pass/deny outcomes, and
duplicate-check clean/exact-clone JSON outcomes. The aggregate is bounded,
sets `SIMPLE_NO_STUB_FALLBACK=1`, and fails closed; a deployed wrapper, raw
source worker, Rust seed, stale binary, or help-only response cannot satisfy it.
The gate establishes command dispatch and minimal behavior only. Release still
requires the full test, lint, and duplication evidence for its scope.

### Temporary Rust test-runner recovery

Normal `simple test` remains pure-Simple. While repairing a stale deployed
self-hosted runner, the Rust bootstrap accepts only the explicit
`SIMPLE_TEST_RUNNER_RUST=1` opt-in and never falls back automatically. Run that
temporary evidence through `scripts/resource/run_capped.shs`, a
`timeout -k 5s ...` wall, and redirected output; inspect only the bounded tail.
Remove the opt-in once the rebuilt pure runner passes the same fixture. Rust
runner output is repair evidence, not production or release qualification.

## Completion Gate

Workflow/tooling changes are not complete until matching process documentation
is fresh. Update `doc/07_guide`, generated/manual SPipe docs under
`doc/06_spec`, `.codex/skills`, `.agents/skills`, `.claude/skills`,
`.claude/agents/spipe`, and `.gemini/commands` where applicable before marking
an agent goal, SPipe phase, verify report, or ship lane complete.
