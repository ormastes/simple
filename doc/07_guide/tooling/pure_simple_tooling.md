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

Light-daemon work carries a tagged absolute expiry. The daemon charges time
spent in its queue, refuses expired work before spawn, and passes only the
remaining budget to `process_run_bounded`. Protocol-unit evidence does not
replace the required end-to-end stale-state and child-cleanup gate.

For the implemented sequential interpreter paths, `--assert-ran` requires an exact private
`SIMPLE_TEST_RESULT_FILE` payload: `simple-bdd-v1`, passed count, failed count,
and one final newline. Counts are canonical nonnegative integers; missing,
malformed, or zero-executed evidence fails. Stdout is presentation, never test
evidence. Other execution modes are not yet authenticated release evidence and
fail closed when `--assert-ran` is requested instead of trusting stdout.

## Mutation and cache safety

Lint JSON mode emits JSON Lines only. `--fix-dry-run` is independent of
`--fix`; applied fixes use the canonical atomic-write facade and a failed write
keeps the command nonzero. Native object-cache keys include optimization level
and effective backend. Dependency-independent `no_mangle` objects may publish
atomically during a failed batch; mangled objects publish only after the whole
batch succeeds.

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

`bin/simple_mcp_server` resolves and enters the canonical repository root
before probing or launching its admitted native server, so relative workspace
paths do not depend on the client's launch directory.

`bin/simple_lsp_mcp_server` is a hash-admitted, bounded native launcher. It
restores the canonical repository-root CWD before execution and admits a
candidate only after correlated `initialize`, `tools/list` (advertising
`lsp_symbols`), and `tools/call(lsp_symbols)` (`log_options_help`) results.
Any JSON-RPC `error`, MCP `isError`, child-command failure text, timeout, or
nonzero child exit fails closed.

Every bootstrap route that produces a Stage 4 full CLI runs
`scripts/check/check-bootstrap-essential-tools-smoke.shs` with the exact fresh
binary. From a temporary non-repository working directory it checks real
test-runner pass/fail/zero/forged outcomes, focused lint pass/deny outcomes, and
duplicate-check clean/exact-clone JSON outcomes. The aggregate is bounded,
sets `SIMPLE_NO_STUB_FALLBACK=1`, and fails closed; a deployed wrapper, raw
source worker, Rust seed, stale binary, or help-only response cannot satisfy it.
The gate establishes command dispatch and minimal behavior only. Release still
requires the full test, lint, and duplication evidence for its scope.

## Current qualification snapshot (2026-07-23)

Source-fixed is not Stage 4 qualification. The following is the current
evidence boundary for the important pure-Simple tooling lanes:

- **test / test-daemon** — **Source status:** canonical direct summaries and
  responsive daemon routing are pushed. **Strongest current evidence:**
  `eceddfd31d` and `7a011de61f`, plus the zero-executed regression in
  [the tracked report](../../08_tracking/bug/test_runner_zero_executed_single_file_greenwash_2026-07-17.md).
  **Remaining bug/gap:** the aggregate Stage 4 essential-tools smoke has not
  passed. **Next solution:** deploy a fresh Stage 4 CLI and run the exact
  essential-tools smoke from its temporary external working directory.
- **check / build / run** — **Source status:** partially fixed; the full
  pure-Simple CLI is not linked/qualified. **Strongest current evidence:**
  Stage 2/3 success and the bounded Stage 4 analysis in
  [the imported-provider report](../../08_tracking/bug/bootstrap_stage4_import_mangling_runtime_gap_2026-07-12.md).
  **Remaining bug/gap:** capability-owned provider composition still blocks the
  full CLI. **Next solution:** complete the canonical provider profile, then
  build and qualify the fresh Stage 4 CLI.
- **lint** — **Source status:** parser-backed ARG001/ARG002 CLI parity is
  implemented; the other AST leaves remain open. **Strongest current evidence:**
  the focused warn/deny/allow, decoy-line, extern-span, and compatibility
  contract passes as bounded bootstrap repair evidence; see
  [the AST dispatch report](../../08_tracking/bug/simple_lint_ast_rules_unwired_2026-07-19.md).
  **Remaining bug/gap:** this is not fresh Stage 4 evidence, and STUB, COLL,
  DTYP, wildcard-import, and wide-public parity is incomplete. **Next
  solution:** qualify ARG through the exact fresh CLI, then extend the same
  CLI-owned parsed adapter one semantic leaf at a time.
- **fmt / fix** — **Source status:** atomic writes and fail-closed source
  rewrites are pushed. **Strongest current evidence:** `5b13444c83` and
  `0a7b45ea7b`. **Remaining bug/gap:** no fresh Stage 4 behavior proof.
  **Next solution:** exercise mutation and write-failure cases through the
  newly deployed pure-Simple CLI.
- **duplicate-check** — **Source status:** effective `mode`/`format`
  validation is pushed. **Strongest current evidence:** `f2818a4b63` and its
  focused bad-value/valid-override probes; see
  [the tracking report](../../08_tracking/bug/duplicate_check_invalid_enum_value_false_green_2026-07-19.md).
  **Remaining bug/gap:** that is focused evidence only, not an aggregate Stage
  4 pass. **Next solution:** run the clean/exact-clone and invalid-option
  essential-tools probes against the exact fresh CLI.
- **MCP** — **Source status:** the full wrapper's repository-root CWD restore
  is pushed. **Strongest current evidence:** `1035de83f1` and the wrapper
  contract above. **Remaining bug/gap:** a fresh Stage 4 native full-MCP
  handshake has not yet been captured as qualification evidence. **Next
  solution:** deploy the exact native server and run its command-line handshake
  from an external CWD.
- **LSP MCP** — **Source status:** bounded native candidate admission is
  pushed. **Strongest current evidence:** `8401b5ebfd` requires correlated
  initialize/list/symbol probes and fails closed. **Remaining bug/gap:** no
  fresh Stage 4 native artifact has completed that admission. **Next
  solution:** build the exact artifact and run the bounded wrapper contract.
- **bootstrap essential gate** — **Source status:** the aggregate gate and its
  fail-closed fixture contract are present. **Strongest current evidence:**
  `scripts/check/check-bootstrap-essential-tools-smoke.shs` is required by this
  guide and the bootstrap build guide. **Remaining bug/gap:** the aggregate
  Stage 4 smoke still has not passed. **Next solution:** run that one bounded
  gate once after a fresh Stage 4 CLI is admitted.
- **Codex session guard** — **Source status:** duplicate-resume locking and
  documented runaway thresholds are pushed. **Strongest current evidence:**
  `879a767a73`, `0e5a2198a5`, and
  [the SQLite/WAL incident report](../../08_tracking/bug/codex_duplicate_resume_sqlite_wal_lock_2026-07-19.md).
  **Remaining bug/gap:** direct Codex invocations outside `bin/codex` remain
  intentionally outside the guard. **Next solution:** use the guarded launcher
  with repo `bin/` first on `PATH`; add broader protection only if direct
  invocation becomes supported.
- **simple-core ABI** — **Source status:** tuple row-length repair is pushed.
  **Strongest current evidence:** `2dc4fc5a4f` and
  [the dict-entry archive report](../../08_tracking/bug/simple_core_value_memory_probe_dict_entries_failure_2026-07-19.md).
  **Remaining bug/gap:** the authoritative archive probe has not rerun past its
  former exit-91 assertion. **Next solution:** perform that incremental exact
  archive qualification before claiming runtime success.

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
