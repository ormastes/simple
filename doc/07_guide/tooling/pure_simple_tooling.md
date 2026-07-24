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

The client publishes requests only by temporary-file rename. A write or rename
failure removes its request artifacts, reports the exact request path, and
returns nonzero; it never falls back to a visible partial request.

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
either the process API timeout marker or the parallel monitor's explicit
deadline state so spawn/internal failures remain ordinary failures.
Pure-Simple callers use the `std.io` facade; hosted C owns the OS capture and
cleanup boundary, and native LLVM calls cross the dedicated tuple ABI facade.

For staged compiler or MCP changes, the bootstrap wrapper must pass its built-in
Stage 2 and Stage 3 compiler sanity, then run the matching stage sanity SSpec
and MCP command-line handshake SSpec. `bin/simple_mcp_server` defaults to the cached
native server; `SIMPLE_MCP_NATIVE` selects an exact artifact for reproducible
verification. The generated POSIX wrapper has no raw-source fallback. The
Windows `.cmd` launcher alone retains an explicit debugging fallback controlled
by `SIMPLE_MCP_ALLOW_SOURCE_FALLBACK=1`, and it may use only a deployed
pure-Simple runtime. No raw-source or Rust-seed launch is production evidence.

`bin/simple_mcp_server` resolves and enters the canonical repository root
before probing or launching its admitted native server, so relative workspace
paths do not depend on the client's launch directory.

`bin/simple_lsp_mcp_server` is a hash-admitted, bounded native launcher. It
restores the canonical repository-root CWD before execution and admits a
candidate only after correlated `initialize`, `tools/list` (advertising
`lsp_symbols`), and `tools/call(lsp_symbols)` (`log_options_help`) results.
Any JSON-RPC `error`, MCP `isError`, child-command failure text, timeout, or
nonzero child exit fails closed.

## Stage 4 essential-tools gate

Every bootstrap route that produces a Stage 4 full CLI runs
`scripts/check/check-bootstrap-essential-tools-smoke.shs` with the exact fresh
binary. From a temporary non-repository working directory it checks real
test-runner pass/fail/zero/forged outcomes, focused lint pass/deny and strict
JSON-Lines outcomes, and duplicate-check clean/exact-clone JSON outcomes. The aggregate is bounded,
sets `SIMPLE_NO_STUB_FALLBACK=1`, and fails closed. Its identity preflight
rejects Rust seed/debug binaries; bootstrap supplies the exact fresh candidate,
and the behavioral probes reject help-only or no-op implementations. The
preflight is not hash provenance for arbitrary wrappers or stale pure binaries.
The gate establishes command dispatch and minimal behavior only for `test`,
`lint`, and `duplicate-check`; release still requires the full evidence for its
scope. Strict JSON parsing and focused malformed-line coverage are source-fixed;
the fresh Stage 4 aggregate remains pending.

## Current qualification snapshot (2026-07-24)

Source-fixed is not Stage 4 qualification. The following is the current
evidence boundary for the important pure-Simple tooling lanes:

- **test / test-daemon** — **Source status:** canonical direct summaries and
  responsive daemon routing and fail-closed atomic request publication are
  pushed. A request write/rename failure cleans artifacts and returns nonzero
  before polling. Positive-timeout hosted capture now waits for pipe EOF or the
  caller deadline instead of truncating delayed descendant output after two
  seconds. **Strongest current evidence:** `eceddfd31d`, `7a011de61f`,
  `f5440b77fa`, and `bd9de761c11`, plus the zero-executed regression in
  [the tracked report](../../08_tracking/bug/test_runner_zero_executed_single_file_greenwash_2026-07-17.md).
  The bounded-capture root fix and evidence are recorded in
  [the delayed-output report](../../08_tracking/bug/stage4_test_runner_bounded_capture_empty_2026-07-23.md).
  **Remaining bug/gap:** neither that fix nor the aggregate essential-tools
  smoke has fresh Stage 4 evidence. Invalid and bare-value test options now
  return exit 2 before configuration or discovery, while signed split values
  remain valid. **Remaining bug/gap:** this preflight has focused source
  evidence only. Public `--format json` is not yet qualified. The pushed
  pure-Simple subprocess boundary captures the worker, routes diagnostics
  to stderr, and emits one aggregate object covering spec and both doctest
  lanes; nested JSON tests fail closed with the same JSON envelope. High static
  review accepted the repaired executable/argv, recursion, and JSON-parser
  boundaries. Bounded seed diagnostics reached valid worker JSON but cannot
  qualify production behavior. The required cached Stage 4 link then timed out
  after 1,800 seconds while parsing
  `src/app/cli/_CliMain/args_and_os_commands.spl`, producing no candidate; see
  [the JSON-format report](../../08_tracking/bug/test_runner_json_format_not_machine_readable_2026-07-24.md).
  **Next solution:** fix the existing global-flags parser/checker timeout,
  build one fresh incremental Stage 4 CLI containing this source repair,
  then run the whole-stdout contract once through that exact binary. Run the
  remaining focused bounded-output and CLI contracts once, then run the exact
  essential-tools smoke from its temporary external working directory.
- **check / build / run** — **Source status:** the full pure-Simple CLI links,
  preserves delegated streams/status, and its isolated official source-check
  passes when `SIMPLE_BINARY` names the candidate. `check` is source-fixed to
  reject unknown, missing, and invalid-domain output options before discovery,
  so a typo cannot silently pass after checking a different scope. Its focused
  option contract passes through the temporary bootstrap interpreter; fresh
  Stage 4 runtime qualification remains pending. Multi-file check dispatch now
  preserves ordered presentation options and last-option-wins JSON selection,
  while unsupported split `--surface VALUE` fails before shared cleaning
  (`0cd092199ad`). This is routing parity only: surface, verbose, and distinct
  LLM rendering remain separate semantic gaps. The paired-value lowering
  fix in `2f6430a87c8` clears the focused p2 enum probe at source. **Strongest
  current evidence:** candidate `00431ce5…`, `2f6430a87c8`, and the bounded repair in
  [the Stage 4 report](../../08_tracking/bug/stage4_full_cli_source_check_blank_exit8_2026-07-23.md).
  **Remaining bug/gap:** no successor full CLI has qualified both the p2 source
  fix and the bounded-output source fix. **Next solution:** incrementally build
  one fresh Stage 4 candidate, run each focused regression once, then run the
  aggregate essential-tools gate. The `run` wrapper now consumes shared log
  options only before the entry file and preserves every post-file program
  token (including `--`) unchanged; its focused source contract awaits the
  same fresh Stage 4 candidate.
- **verify** — **Source status:** the public verification CLI now validates its
  grammar before worker dispatch. Unknown, bare/empty `--files`, duplicate, and
  conflicting scope options return exit 2 rather than silently falling back to
  changed-file or empty PASS scope; status/list/check/regenerate reject tails,
  and help is valid only by itself. `--all` supplies Git-tracked project files
  to the tooling gate rather than the current diff, so a clean checkout cannot
  skip tooling-sensitive paths while claiming full-project scope.
  **Strongest current evidence:** the focused contracts in
  `test/01_unit/app/verify_cli_option_validation_contract_check.spl` and
  `test/01_unit/app/verify_all_scope_contract_check.spl`.
  **Remaining bug/gap:** fresh Stage 4 runtime qualification is pending; see
  [the verify option report](../../08_tracking/bug/verify_cli_option_false_green_2026-07-23.md).
- **lint** — **Source status:** parser-backed ARG001/ARG002, COLL001-COLL008,
  STUB001/STUB002, and module-level W0404 wide-public CLI parity are implemented; W0404 reports at
  line 1, honors `visibility_boundary`, and suppresses `__init__.spl`/`mod.spl` facades.
  Query/LSP STUB001/STUB002 collection now reports the checker's declaration
  span instead of a same-name comment/string text match.
  The generic EasyFix rule remains the sole public duplicate-typed argument
  owner; the DTYP query/LSP leaf now ignores named calls. The generic
  `pass_todo` check remains the STUB003 owner so findings are not duplicated.
  Wildcard import/export parity is wired through W0406/W0407 with facade
  suppression. **Strongest current evidence:**
  the focused warn/deny/allow, decoy-line, extern-span, compatibility, and
  STUB, W0404, and wildcard line/config/facade contracts are bounded bootstrap
  repair evidence; the
  query STUB decoy-line contract passes on the Rust seed, while the deployed
  pure-Simple wrapper still segfaults before that contract executes; see
  [the AST dispatch report](../../08_tracking/bug/simple_lint_ast_rules_unwired_2026-07-19.md).
  Parse failure now denies with PARSE001 (`57a4761a38d`), invalid or missing
  CLI options return exit 2 (`6dd99e39653`), and invalid project lint config is
  rejected (`ef2ef732608`). The shared lint owner validates mixed help before
  returning help (`3721a305413`); the public lint/fmt/fix entry now preserves
  sole help while routing mixed-help forms to closed option validation.
  The same change set corrected active Codex/Claude/Gemini/SPipe guidance to use direct
  `bin/simple lint`; `build lint` remains the Rust clippy lane. Shared
  worker/fallback help handling matches the public lint entry
  (`cc69749ef25`); each has focused contract evidence. **Remaining
  bug/gap:** these fixes, `982ce3fa445`, and the focused wildcard contract are
  not fresh Stage 4 evidence. **Next solution:** qualify
  ARG/COLL/STUB/W0404/W0406/W0407 and the parse/CLI/config contracts through
  the exact fresh CLI, then extend the same CLI-owned parsed adapter one
  semantic leaf at a time.
- **fmt / fix** — **Source status:** atomic writes, fail-closed source
  rewrites, and closed `fmt`/`fix` option parsing are source-fixed. Invalid or
  malformed fmt options return exit 2 before a file read/write/output; help
  returns 0 only when used alone, while mixed help fails closed
  (`a974dddfec6`); invalid or empty fix options return exit 2 before
  a file read/write; exact `--dry-run` remains
  non-mutating. **Strongest current evidence:** `5b13444c83`, `0a7b45ea7b`,
  and `3bd9be7c52c`.
  Both fix-option owner contracts pass through the temporary bootstrap
  interpreter after routing writes through the module-level facade. **Remaining
  bug/gap:** the fmt validator and both isolated owner contracts also pass
  through that temporary interpreter; the retained pure-Simple binary crashes with the
  separately tracked stale `rt_env_set` ABI before either contract executes,
  so there is no fresh Stage 4 behavior proof. **Next solution:** deploy a
  candidate that passes frontend admission, then exercise option, mutation,
  and write-failure cases once through that exact CLI.
- **duplicate-check** — **Source status:** effective `mode`/`format`
  validation, actual token-mode `min_tokens` enforcement, same-file semantic
  matching, and cosine fragment grouping are fixed. Overlapping cosine
  candidates are threshold-scored before physical occurrences collapse, and
  the legacy 320-block sampler no longer drops late candidates. The top-five
  signature index and 400-block bucket cap still bound comparisons. Similarity,
  semantic, and semantic-drift thresholds now reject non-finite and
  out-of-range values (`60f23743d1d`). **Strongest current evidence:**
  `f2818a4b63`, `6a9af6f6635`, `74594ec99ff`, and `60f23743d1d`; the focused
  detector and threshold contracts passed through the temporary bootstrap
  interpreter. The configured lexical SDN report path now writes once,
  propagates write failure, and has focused temporary-bootstrap evidence; see
  the [report-path report](../../08_tracking/bug/duplicate_check_report_path_silent_noop_2026-07-23.md).
  See the [token threshold report](../../08_tracking/bug/duplicate_check_token_mode_min_tokens_ignored_2026-07-23.md)
  [cosine fragment report](../../08_tracking/bug/duplicate_check_cosine_fragmented_occurrence_groups_2026-07-23.md),
  and [similarity threshold report](../../08_tracking/bug/duplicate_check_similarity_threshold_false_clean_2026-07-23.md).
  Sole help remains exit 0, while mixed help and invalid arguments now return
  exit 2 before parser exit (`f2e15a08c4c`).
  The unreachable `src/app/cli/duplicate_check.spl` parser, which silently
  ignored unknown flags and diverged from the compiler-owned command, is
  deleted; the portability contract now prevents that parallel entrypoint from
  returning (`4094d5a779e`).
  **Remaining bug/gap:** fresh Stage 4 evidence is missing, and incremental-cache
  flags remain deliberately rejected because their detector/cache path is
  disconnected; see [the cache report](../../08_tracking/bug/duplicate_check_incremental_cache_disconnected_2026-07-23.md).
  **Next solution:** run the focused and essential-tools probes against the
  exact fresh CLI. Enable caching only after a non-cyclic grouping path and a
  two-run cache/invalidation smoke pass.
- **MCP** — **Source status:** the full wrapper's repository-root CWD restore
  is pushed. Direct server admission now rejects residual/tail arguments before
  entering stdio; help/version/probe are accepted only when shared-log cleaning
  leaves them as the sole server argument (`2d1a6a7afd7`).
  **Strongest current evidence:** `1035de83f1`, `2d1a6a7afd7`, and the wrapper
  contract above. **Remaining bug/gap:** a fresh Stage 4 native full-MCP
  handshake has not yet been captured as qualification evidence. **Next
  solution:** deploy the exact native server and run its command-line handshake
  from an external CWD.
- **LSP MCP** — **Source status:** bounded native candidate admission is
  pushed. Direct entry and generated wrappers now reject/delegate malformed
  tails, validate documented log modes, and reject unsupported split surface
  before serve (`2d1a6a7afd7`). **Strongest current evidence:**
  `2d1a6a7afd7` covers admission/log grammar, while `8401b5ebfd` requires
  correlated initialize/list/symbol probes and fails closed. **Remaining bug/gap:** no
  fresh Stage 4 native artifact has completed that admission. **Next
  solution:** build the exact artifact and run the bounded wrapper contract.
- **bootstrap essential gate** — **Source status:** the aggregate gate and its
  fail-closed fixture contract are present. It now runs a bounded identity
  preflight with seed-warning suppression neutralized, rejects Rust seed/debug
  identities before any test/lint/duplicate probe, and emits an explicit
  pure-Simple identity marker (`ca7ce8d432b`). The shared probe boundary and
  standalone JSON validator now clear inherited `SIMPLE_BOOTSTRAP` and
  `SIMPLE_RUNTIME_PATH`, preventing bootstrap-only compiler or runtime semantics
  from qualifying as production behavior; see the
  [bootstrap-mode report](../../08_tracking/bug/stage4_essential_tools_inherited_bootstrap_mode_false_green_2026-07-24.md).
  **Strongest current evidence:**
  the portability contract exercises seed-signature rejection before any tool probe;
  `scripts/check/check-bootstrap-essential-tools-smoke.shs` remains required by
  this guide and the bootstrap build guide. **Remaining bug/gap:** the aggregate
  Stage 4 smoke still has not passed; strict JSON parsing and focused
  malformed-line coverage are source-fixed only; see the
  [lint JSON report](../../08_tracking/bug/bootstrap_lint_json_validation_false_green_2026-07-23.md).
  **Next solution:** deploy a fresh Stage 4 CLI, then run the one bounded gate
  once.
- **examples-check** — **Source status:** pure-Simple command routing is
  implemented and malformed command options now fail closed before discovery.
  Timeout is bounded to positive milliseconds-safe seconds; limit is bounded
  nonnegative with only zero meaning unlimited (`b06cce875ca`).
  Its focused option contract passes through the temporary bootstrap
  interpreter. **Remaining bug/gap:** no fresh pure-Simple qualification evidence.
  **Next solution:** run one focused passing example and one failing example
  through the exact fresh CLI, preserving their exit statuses.
- **spipe-docgen** — **Source status:** pure-Simple `simple-core` or
  `core-c-bootstrap` routing is implemented and unknown options fail closed
  before generation. **Remaining bug/gap:** no fresh qualification evidence.
  **Next solution:** generate one fixture document with the exact runtime and
  assert the expected output exists and is nonempty.
- **native-build** — **Source status:** pure-Simple command routing and cached
  artifact path are implemented. Final artifacts now build in a process-unique
  sibling and publish by direct rename, so stale requested outputs cannot
  satisfy a driver `Success` without a fresh artifact. Its option preflight
  rejects unknown, missing, empty, option-looking, and invalid numeric option values before
  compilation or output mutation. Compile/link failures preserve the prior requested output. **Remaining bug/gap:** the focused
  staging source-contract scenario passes, but no fresh behavioral build is
  qualified. **Next solution:** incrementally build one small entry closure
  with the exact fresh CLI, then run its artifact once.
  A sole `--help`/`-h` succeeds; malformed invocations (including malformed
  `... --help`) fail with exit 2. `--emit-archive` remains active archive mode;
  legacy `--linker-script`, `--runtime-path`, and `--no-incremental` remain
  arity-checked compatibility no-ops in this pure-Simple path.
- **latest full Stage 4 candidate (2026-07-23)** — candidate SHA
  `00431ce52f940722f52746a802011f7d33f35d4931738facee26c5c7b7917b31`
  passes delegated stream/status fidelity and the isolated official
  source-check. Admission still rejects it on the p2 native-build SIGILL and
  bounded test-child result loss; frontend/redeploy/essential-tools gates are
  not credited. Both roots now have source fixes (`2f6430a87c8` and
  `bd9de761c11`), but no successor full candidate is qualified. See the
  [candidate failure report](../../08_tracking/bug/stage4_full_cli_source_check_blank_exit8_2026-07-23.md).
- **Codex session guard** — **Source status:** duplicate-resume locking and
  documented runaway thresholds are pushed. The watchdog now closes its
  inherited lock descriptor, so an exited session cannot leave a sleeping
  child holding the resume lock (`0f473de24c7`). **Strongest current evidence:**
  `879a767a73`, `0e5a2198a5`, `0f473de24c7`, and
  [the SQLite/WAL incident report](../../08_tracking/bug/codex_duplicate_resume_sqlite_wal_lock_2026-07-19.md).
  **Remaining bug/gap:** direct Codex invocations outside `bin/codex` remain
  intentionally outside the guard. **Next solution:** use the guarded launcher
  with repo `bin/` first on `PATH`; add broader protection only if direct
  invocation becomes supported.
- **simple-core ABI** — **Source status:** tuple row-length repair is pushed.
  **Strongest current evidence:** `2dc4fc5a4f` and
  [the dict-entry archive report](../../08_tracking/bug/simple_core_value_memory_probe_dict_entries_failure_2026-07-19.md).
  **Remaining bug/gap:** the authoritative archive probe rerun exposed a local
  runtime-symbol resolution panic before its former exit-91 assertion; that
  resolver is source-fixed but its Rust test has not executed because the
  existing test binary failed to link. **Next solution:** restore the Rust test
  link, then rerun the exact incremental archive qualification before claiming
  runtime success.

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
