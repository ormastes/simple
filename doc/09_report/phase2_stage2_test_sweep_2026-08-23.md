# Phase-2 (Stage 2) pure-Simple compiler — attempted full test sweep
Date: 2026-08-23. Binary: /mnt/data/bootstrap-run28/stage2/x86_64-unknown-linux-gnu/simple
(132,930,184 bytes, ELF x86-64, not stripped, BuildID ca445649ca0d14d0c1c3cf913eb18d2f438ac6a0)
Worktree: /mnt/data/worktrees/phase2tests-1 (detached, 371825c23db). run28 untouched.

## VERDICT
NO TEST SWEEP WAS POSSIBLE. 0 specs executed. Per the measurement rules, zero items
examined is an ERROR, never a pass. The delta vs the seed baseline is UNMEASURABLE.

## 1. What the binary actually supports (VERIFIED)
Dispatch read at src/app/cli/bootstrap_main.spl:497-521 (main()).
Exactly four accepted first-args:
  native-build   -> run_native_build_bootstrap  (line 500-501)
  --version      -> prints version              (line 502-504)
  --help         -> usage                       (line 505-515)
  compile        -> run_compile_bootstrap       (line 516-517)
anything else -> "error: unknown command" exit 1 (line 518-520).
`compile` accepts --format=smf ONLY (run_compile_bootstrap, line ~441).
No run/test/lint/fmt/build. VERIFIED: `--version` -> "simple-bootstrap 1.0.0-RC", rc=0.

## 2. Harness attempted
Since the binary has no `test`, the only possible harness is: use it as the compiler
under test — `native-build <spec>.spl -o bin && ./bin` — one native executable per spec.
That harness never got off the ground: it cannot compile a 3-line hello world.

## 3. Blocking defects (all VERIFIED, exit status read directly into a variable, never piped)

### D1 — SEGV in HIR cache encoder (default config)
  $B native-build hw.spl  -> rc=139 (SIGSEGV), 1.66s wall, RSS 159,488 KB
  $B compile hw.spl --format=smf -> rc=139 (SIGSEGV)
  gdb backtrace:
    #0 compiler.hir.generated.hir_codec.hc_enc_hir_type
    #1 compiler.hir.generated.hir_codec.hc_enc_hir_symbol
    #2 compiler.hir.generated.hir_codec.hc_enc_symbol_table
    #3 compiler.hir.generated.hir_codec.hc_enc_hir_module
    #4 compiler.hir.hir_codec.hir_module_encode
    #5 compiler.driver.driver_hir_cache.hir_cache_store
    #6 CompilerDriver.lower_and_check_impl
    #7 CompilerDriver.compile
    #8 app.cli.bootstrap_main.run_native_build_bootstrap
  Workaround found: SIMPLE_HIR_CACHE=0 (gate at
  src/compiler/80.driver/driver_hir_cache.spl:77-78) bypasses this crash.
  Crash is in generated HIR codec, on the CACHE-WRITE path only.

### D2 — SEGV in AOT native codegen (with D1 worked around)
  SIMPLE_HIR_CACHE=0 $B native-build hw2.spl -> rc=139, 9.08s wall, RSS 370,928 KB
    (hw2 = same hello world with explicit `return 0`)
  gdb backtrace:
    #0 compiler__driver__driver_aot_native_output___compile_frozen_module_capsule
    #1 CompilerDriver.compile_to_native
    #2 run_native_build_bootstrap
  Also SEGVs on `compile --format=smf` with the cache off (rc=139).
  => No output artifact is producible by EITHER supported command, in EITHER config.

### D3 — implicit tail-expression return rejected (self-hosting regression)
  `fn main() -> i64:` ending in a bare `0` (no `return`) is accepted and RUNS on the
  Rust seed (`bin/simple run hw.spl` prints "hello"), but stage2 rejects it:
    "MIR error: E-SFFI-016: missing return in non-unit function 'main'"
  Confirmed delta seed-passes / self-hosted-fails.

### D4 — stdlib does not resolve for a real spec
  SIMPLE_HIR_CACHE=0 $B native-build test/01_unit/compiler/frontend/aop_conflict_detect_spec.spl
  -> rc=1, HIR lowering errors: unresolved name `file_read_result`,
     `read_file_text_result`, `runtime_file_rename` in
     src/std/nogc_sync_mut/io/file_ops.spl:7:8.
  Separately, an ABSOLUTE spec path yields "collected zero source files" — the entry
  resolver requires a repo-root-relative path.

## 4. Counts requested (all zero-by-absence — labelled as such)
  specs executed: 0        passed: 0      failed: 0     hung: 0
  examples: 0              phantom verdicts (passed with 0 examples): 0 BY ABSENCE
  SIGTERM/SIGKILL deaths (earlyoom): 0 observed
  peak RSS measured: 370,928 KB (D2 crash), 159,488 KB (D1 crash) — compiler process only
  hangs/deadlocks: none; every failure was a fast crash (1.7s / 9.1s), not a hang
  DELTA vs seed baseline (2179/1763/412/4, 16528 ex): NOT MEASURABLE.

## 5. Could not measure
Everything spec-level. The gate is D1+D2: the compiler cannot emit any artifact for
even a trivial program, so no spec can be built, let alone run. D2 must be fixed before
any phase-2 sweep number exists. D1 is separately fixable and has a working env bypass.

## 6. Notes
- /mnt/data/bootstrap-run28 preserved untouched. /mnt/data/worktrees/outlinefix-1 untouched.
- No fix landed, so no reproduce test and no plan-doc row are due.
- No commits, no pushes; no gates run (nothing to gate).
- earlyoom not implicated: both deaths were SIGSEGV (11), not SIGKILL/SIGTERM.
