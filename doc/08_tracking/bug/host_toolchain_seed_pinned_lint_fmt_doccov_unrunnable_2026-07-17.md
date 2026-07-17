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
