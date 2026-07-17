# Host toolchain seed-pinned: lint/fmt/doc-coverage/test (and .spl-only CLI surface) unrunnable

**Date:** 2026-07-17
**Severity:** high (four tooling lanes dead on the host; masked by the seed-stopgap deploy)
**Status:** open

## Symptom

With `bin/simple` currently a Rust-seed stopgap (deployed 2026-07-11) and the
fresh seeds at `src/compiler_rust/target/{release,bootstrap}/simple` (2026-07-17):

- `bin/simple lint <file>` / `bin/simple fmt --check <file>` (deployed): dies with
  `error: semantic: unknown extern function: rt_cli_arg_count` — the Jul-11
  binary's extern allowlist predates the scalar CLI-arg externs (7714fcb2783).
- `<fresh seed> lint|fmt`: fails closed with
  `error: rt_cli_run_lint is not supported in interpreter mode` /
  `rt_cli_run_fmt ...` — these subcommands require the native-compiled CLI.
- `<any seed> doc-coverage`: `error: file not found: doc-coverage` + usage dump,
  exit 1. The seed front-end treats subcommands it does not know as script
  paths, so the pure-Simple dispatch handler
  (`src/app/cli/_CliMain/main_and_help.spl:270 run_doc_coverage`) is never
  reached. The same applies to the whole .spl-only subcommand family when the
  active binary is a seed.
- `simple check <file>` works (exit 0) on the fresh seed — the pure-Simple
  check path is healthy.
- `bin/simple test <spec>` (deployed 2026-07-11 stale binary): same
  `error: semantic: unknown extern function: rt_cli_arg_count` as
  lint/fmt above — confirmed independently 2026-07-17 (TESTRUNNER lane).
  `<fresh seed> test <spec>` (default interpreter mode): does **not** hit
  rt_cli_arg_count (that extern is registered in current
  `runtime_symbols.rs`/`interpreter_extern`), but instead walks a much
  larger transitive dependency closure than expected and dies with
  `error: compile failed: parse: in ".../gpu_portable_compute.spl":
  Unexpected token: expected expression, found TripleLt`. That file
  parses clean in isolation (`simple check gpu_portable_compute.spl` →
  all checks passed) — the error location is misattributed by the
  interpreter's whole-tree walk, so treat it as a symptom of the same
  "no true self-hosted binary" gap, not a real bug in that file.
  **Working interim for verifying `.spl` test content:**
  `<fresh seed> run <spec>` (not `test`) executes `describe`/`it` blocks
  directly as top-level script code and prints real pass/fail per
  example. Confirmed 2026-07-17 on all 4
  `test/01_unit/compiler/regression/*.spl` files: 31/31 examples pass
  (entry_closure_defect_semantics 13, short_circuit_semantics 7,
  struct_init_omitted_field_nil_fill 7, try_operator_preservation 4).
  **Caveat — this only proves the interpreter-level contract, not full
  coverage:** `run` executes these specs through the tree-walking
  interpreter. Several of the 4 files explicitly pin *compiled/native-build*
  regressions (e.g. `entry_closure_defect_semantics_spec.spl` documents
  "entry-closure codegen defects"; `short_circuit_semantics_spec.spl`'s own
  header notes the interpreter path "was already correct" and the spec pins
  that contract specifically because the *compiled* path was the one that
  regressed). The compiled/native-build path some of these regressions
  target is walled by the same Stage 2/3/4 blockers above and remains
  unverified — `run` (interpreter) passing is real signal but is not a
  substitute for the native `test`/`--compile` path once redeploy is
  unblocked.

## Root cause

Not a defect in the .spl tooling itself: the host has no current true
self-hosted `bin/release/<triple>/simple`. The known whole-compiler redeploy
wall (#99 family; see
`doc/08_tracking/bug/deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`)
means lanes that need either (a) a fresh extern allowlist or (b) native CLI
hooks (`rt_cli_run_lint`/`rt_cli_run_fmt`) or (c) the .spl CLI as the real
entrypoint are all pinned to a stale/incapable binary.

## 2026-07-17 redeploy-attempt findings (TESTRUNNER lane)

Checked whether a cheap redeploy could close the `test` gap without touching
the strategic dynSMF work:

- `scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload` (incremental,
  reuses existing seed, no cargo) now fails at Stage 2 with
  `error: native backend 'llvm' is not available in this build; rebuild the
  Rust driver with --features llvm or use --backend cranelift` — the
  `target/bootstrap/simple` seed profile lacks the llvm cargo feature this
  run, so Stage 2/3 native-build never starts. `--backend=cranelift` was not
  attempted (out of scope for this lane; flagging for whoever owns the
  redeploy).
- A leftover artifact from the last *successful-looking* chain,
  `build/bootstrap/full/x86_64-unknown-linux-gnu/simple` (2026-07-16 08:00,
  no seed-warning banner, `--version` prints `Simple v1.0.0-beta`), is **not**
  usable — its own `stage4-native-build.log` records
  `Segmentation fault (core dumped)` for that build, and it fails the
  documented stage4 smoke gate: `-c 'print(1+1)'` does not print `2` (falls
  through to seed-sibling-delegation warnings instead), and `test <spec>`
  mis-fires its own `SIMPLE_TEST_DEPTH` recursion guard on every invocation
  (verified via `strace -f -e trace=execve,clone,fork,vfork`: exactly one
  `execve`, so it is an in-process double-dispatch, not a subprocess
  re-spawn — consistent with the entry-closure/self-host miscompile family in
  `deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`, not a new
  independent bug). Do not deploy this artifact.
- Unrelated but adjacent: commit `121e6297878` ("fix(cli): restore safe test
  depth text", 2026-07-17 03:24 UTC) already fixed a real source bug in both
  `main_and_help.spl` and `test_entry.spl` — `env_set("SIMPLE_TEST_DEPTH",
  "{_depth + 1}")` (string-interpolated expression) → `env_set(...,
  (_depth + 1).to_text())`. This predates and is unrelated to the
  build/bootstrap/full segfault above (that artifact is from 2026-07-16,
  before the fix existed either way) — noted here only so a future rebuild
  doesn't re-diagnose it.

## Fix direction

1. Strategic (in progress 2026-07-17): dynSMF toolchain entries
   (`lint_tool`, `fmt_tool`, `fix_tool`, `todo_scan`, `mcp_diag_tools`) so
   tool updates load as small precompiled modules instead of requiring the
   whole-compiler redeploy.
2. Tactical: refresh the deployed stopgap from the current seed build
   (cp to `.new` + `mv`) so at least the extern-allowlist class of failures
   (lint/fmt/test on deployed) moves to the interpreter-mode class until the
   true self-hosted redeploy lands. Note this does not fix `test`
   end-to-end — the fresh seed's default (interpreter) `test` mode still
   hits the misattributed whole-tree-walk parse error above; `run <spec>`
   remains the only clean verification path for `.spl` test content until
   the self-hosted binary is real again.
3. The self-hosted redeploy itself remains the real fix (do not race it; see
   memory/#99).

## How found

Tooling-surface smoke matrix (check / sdoctest / md / doc / test / compile /
run) during the 2026-07-17 test-runner hardening campaign.

## Runnable pure-Simple lint path 2026-07-17

Worker M mapped the lint architecture and confirmed `simple lint` (both the
deployed stopgap and the `rt_cli_run_lint`-gated seed CLI subcommand) are not
the only way in: the pure-Simple lint entry (`src/app/cli/lint_entry.spl` ->
`app.io.cli_lint_commands` -> `compiler.tools.lint.main`) can be run directly
through the fresh seed's `run` subcommand, bypassing the seed's native `lint`
CLI dispatch entirely:

```
timeout 240 src/compiler_rust/target/release/simple run src/app/cli/lint_entry.spl lint <target.spl>
```

Verified: exit 0 + "Lint passed: all files clean" on `test/fixtures/lint/clean.spl`;
exit 1 + both violations named (`W001`, `D001`) + "Lint failed in 1 file(s)"
on `test/fixtures/lint/dirty.spl`. `simple fmt`/`simple fix` follow the same
pattern (`src/app/cli/lint_entry.spl {fmt|fix} <target>`).

This path was **not actually working** before three root-cause pure-Simple
fixes landed today (all three are real bugs independent of the redeploy
wall above, so they are recorded here rather than re-filed):

1. **`run_lint_file` imported but never defined.**
   `src/app/io/cli_lint_commands.spl` did `use lazy compiler.tools.lint.main.{run_lint_file}`
   and called it, but no such function existed anywhere in the tree —
   `Linter.lint_file()` was the only real per-file entry point, reachable
   only from the standalone `entry_and_fixes.spl main()`, never from the
   `simple lint` CLI wrapper. Fixed by extracting the report/exit-code logic
   from `entry_and_fixes.spl main()` into a real, shared
   `fn run_lint_file(file_path: text, args: [text]) -> Int`
   (`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`), reused by
   both `main()` and the CLI wrapper.

2. **Global function-name collision: `cli_run_lint`/`cli_run_fmt`/`cli_run_fix`.**
   The same three names were defined THREE times: the intended pure-Simple
   impl (`app.io.cli_lint_commands`), an extern-calling stub
   (`std.nogc_sync_mut.{sffi,ffi}.cli`, wrapping the `rt_cli_run_lint`
   family that is deliberately unsupported in interpreter mode), and a third,
   fully independent legacy implementation
   (`src/app/io/_CliCommands/run_commands.spl`, re-exported through
   `app.io.__init__`). `src/app/cli/lint_entry.spl` imports
   `std.cli.cli_util` (which pulls in `std.sffi.cli`) alongside
   `app.io.cli_lint_commands` — with same-named functions across modules,
   the seed's function registry is evidently flat/global rather than
   module-scoped, so the call resolved to the extern-stub, surfacing as
   `error: rt_cli_run_lint is not supported in interpreter mode` even though
   the real implementation was reachable and correct. This is the same
   landmine class as the documented "same class name in 2 modules collides
   globally" issue, here hitting plain functions. Root-fixed (pure Simple,
   no interpreter change) by renaming the pure-Simple impls to
   `run_lint_command`/`run_fmt_command`/`run_fix_command` in
   `app.io.cli_lint_commands.spl`, with call-site updates in
   `src/app/cli/lint_entry.spl` and `src/app/cli/lint_worker.spl` (the
   dynSMF `lint_tool` worker entry). The interpreter's non-module-scoped
   function registry itself is a Rust-side defect, out of scope here (no
   Rust changes) — flagging for anyone touching the interpreter's symbol
   table: same-named top-level functions across unrelated modules can
   silently shadow each other with no compile-time diagnostic.

3. **`read_file` collision zeroing out all lint findings.**
   `compiler.tools.lint._LintMain.config_and_model.spl` had its own private
   `fn read_file(path) -> LintReadFileResult` (used internally by
   `Linter.lint_file()`), while `compiler.tools.formatter.main` separately
   exports a `fn read_file(path) -> Result<String, String>` — a different
   enum entirely. `app.io.cli_lint_commands.spl` imports both (`formatter.main`
   for `fmt --diff`, `lint.main` for lint). Whichever module's `read_file`
   registers last in the same global registry wins; when it was formatter's
   version, `Linter.lint_file()`'s `match file_content: case LintReadFileResult...`
   never matched (wrong enum type), so `lint_file()` silently returned as
   if the file were clean — real violations vanished with no error, no
   diagnostic, exit 0. Reproduced with a 2-line minimal repro (two sibling
   `use compiler.tools.formatter.main.{...}` / `use compiler.tools.lint.main.{run_lint_file}`
   imports in one file). Root-fixed by renaming the lint-internal helper to
   `lint_read_file` (`config_and_model.spl` + its one call site in
   `lint_checks.spl`). This is the actual "if lint NEVER returns nonzero on
   violations, that is a bug" greenwash scenario flagged in the task brief —
   confirmed fixed: `dirty.spl` now correctly exits 1.

**Known interpreter limitation, not a lint defect:** any `app.io.mod.process_run`
(or `app.io.cli_ops._cli_process_run`) call made from inside a `describe`/`it`
block, when the spec file is run through the Rust seed's interpreter (`simple
test`/`simple run`), taints the whole script's own process exit code — the
individual examples pass and print correctly, but the file's own exit code
goes nonzero, which the test-runner's fail-closed `code != 0 and failed == 0`
check (`src/app/test_runner_new/test_runner_single.spl`) reports as an overall
spec failure. Reproduced independently on the pre-existing, unrelated
`test/01_unit/app/io/process_limits_enforcement_spec.spl` (14/14 examples
pass, file-level result still FAIL under the seed) — this is the documented
"Interpreter mode limitation" in `.claude/rules/testing.md`, not something
introduced by `test/03_system/app/lint_cli_contract_spec.spl`. That spec's two
examples both pass and correctly assert the CLI contract; only the
seed-interpreter's own file-level exit code is unreliable when a subprocess is
spawned from a `describe`/`it` block. Not fixable in pure Simple (interpreter
change required, out of scope here) — filing here rather than a new doc since
it is the same "seed interpreter mode is not the real tool" family as this
bug's title.
