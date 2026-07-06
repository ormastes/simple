# Pure Simple Tooling Contract

This guide records the production contract for `bin/simple` tooling.

## Runtime Boundary

`test`, `test-daemon`, `check`, `examples-check`, `fmt`, `lint`, `fix`,
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

## Bootstrap Build Modes

`scripts/bootstrap/bootstrap-from-scratch.sh` is pure-Simple-only by default and
does not rebuild Rust. Use `--full-bootstrap` for the rare Rust seed/runtime
rebuild.

Pure-Simple rebuilds use two mode names:

- `dynload` (default): faster iteration; keep reusable native cache entries
  unless compiler/app/lib/AOP/loader/interpreter inputs changed, and have
  native-build emit native plus SMF cache artifacts where supported.
- `one-binary`: conservative monolithic native executable; clear the native
  cache before stages.

Native-build cache artifacts default to `build/native_cache`. Bootstrap
overrides that to `build/bootstrap/native_cache` so staged compiler artifacts
stay under the bootstrap build tree. Use bootstrap `--fresh-cache` when you
want a clean dynload cache without rebuilding the Rust seed/runtime; use
`--full-bootstrap` only when Rust seed/runtime inputs must be rebuilt.

Dependency tracing is conservative around AOP/MDSOC weaving. Textual entry
closure is only a reducer; changes under `src/compiler` that can affect weaving,
the loader, the interpreter, or compiler ABI invalidate broadly instead of
pretending only the changed source file needs rebuilding.
Bootstrap script cache stamps also include `src/app`, `src/lib`, and
AOP/MDSOC/weaving/loader/interpreter/native-build environment knobs because
those inputs can change emitted CLI/runtime behavior even when the compiler
layer itself is unchanged.

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
