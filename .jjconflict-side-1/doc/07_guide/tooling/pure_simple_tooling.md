# Pure Simple Tooling Contract

This guide records the production contract for `bin/simple` tooling.

## Runtime Boundary

`test`, `test-daemon`, `check`, `examples-check`, `fmt`, `lint`, `fix`,
`verify`, `spipe-docgen`, `native-build`, `vscode`, `electron`, and `security`
must route to pure Simple entrypoints by default. The Rust compiler under
`src/compiler_rust/` is a seed/bootstrap implementation only. It must not be
used as a fallback for migrated public tools.

When a migrated tool is slow, flaky, or resource-heavy, fix the pure Simple
implementation in `src/compiler`, `src/lib`, or `src/app`, or record a concrete
bug. Do not re-enable a Rust escape hatch.

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

## Completion Gate

Workflow/tooling changes are not complete until matching process documentation
is fresh. Update `doc/07_guide`, generated/manual SPipe docs under
`doc/06_spec`, `.codex/skills`, `.agents/skills`, `.claude/skills`,
`.claude/agents/spipe`, and `.gemini/commands` where applicable before marking
an agent goal, SPipe phase, verify report, or ship lane complete.
