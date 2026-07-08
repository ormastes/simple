# Stage4 Self-Host Redeploy (#79) — Detailed Plan (2026-07-08)

Status: **blocked, precisely root-caused.** Deployed `bin/simple` (Jul 3) still
works as a tool; producing a *new* self-hosted stage4 binary from current source
does not yet succeed. This plan records the two emit paths, the exact current
wall, and the concrete next steps with file:line anchors.

## Goal

`bin/simple build bootstrap` (or the equivalent stage2 self-compile) produces a
working self-hosted `simple` binary from current `src/`, gateable and
redeployable to `bin/release/<triple>/simple`.

## The two emit paths

1. **cranelift/llc `SIMPLE_BOOTSTRAP=1` (the bootstrap path).** Driver:
   `src/compiler/80.driver/driver_bootstrap.spl`
   (`bootstrap_emit_real_llvm_object`, :226). Uses the pure-Simple `MirToLlvm`
   text backend + `llc`. This is the realistic route to a redeployable stage4.
2. **llvm-lib AOT (reference-correct sibling).** `src/compiler/70.backend/
   backend/llvm_lib_*`. Now compiles *trivial* programs to running binaries
   (commits `7984ab3`, `4866213`) but is long-horizon for #79 — and the deployed
   `bin/simple` has **no LLVM linked**, so it can't even run this backend.

## CURRENT WALL — string literals dropped in the stage2 self-compile

**Evidence.** The `SIMPLE_BOOTSTRAP=1` stage2 self-compile of
`src/app/cli/bootstrap_main.spl` returns rc=0 and emits a **21KB inert stub**:
run it and `--version`/no-arg print nothing. Dumped IR (`/tmp/simple_llvm_*.ll`)
shows:
- `fn bootstrap_version()->text: "1.0.0-beta"` → `ret ptr null` (string→null on
  the return path).
- `__simple_main` has a real body, but every `rt_println` arg is a `[1 x i8]`
  (empty `""`) global; short *compared* literals (`--version` `[10 x i8]`,
  `--help` `[7 x i8]`) survive with content.
- `fn native_build_help()->i64: 0` → `ret i64 0` is **correct** (not a bug).

**The codegen emitter is innocent.** Path: `driver_bootstrap.spl:232` creates a
`MirToLlvm` translator → Str emit at
`70.backend/backend/_MirToLlvm/core_codegen.spl:553` → `add_string_global`
(`asm_constraints_helpers.spl:151`), whose array size is
`escaped_string_byte_len(v)+1 = value.len()+1`
(`mir_to_llvm_helpers.spl:135`). `[1 x i8]` ⟹ `value.len()==0` **at emission**,
so the `Const(Str)` is **already empty** when it arrives.

**So the drop is upstream.** The MIR functions are pre-built and stored in
`_bootstrap_mir_functions` (`50.mir/_MirLowering/bootstrap_globals.spl:41`,
added at `:145`) from the standard HIR→MIR lowering. String literals become
`MirConstValue.Str(value)` at `50.mir/mir_data.spl:486` (`emit_const_str`,
:482). Either HIR→MIR builds an empty `Const(Str)`, or the **seed interpreter
zeroes string literals** while running the (interpreted) compiler during the
self-compile — the #66 "string drops to empty in run path" class, residual on
the `SIMPLE_BOOTSTRAP` compile path (#66 was closed for the concat case).

## Why it's been hard (structural, not just difficulty)

- **Duplicate module files**: numbered (`50.mir`, `70.backend`) vs non-numbered
  (`mir`, `backend`) directories both exist. The seed resolves an import to one
  copy; instrumentation on the other copy silently never fires (both `ADDSTR`
  in `add_string_global` and `EMITSTR` in `emit_const_str` missed). Same #41
  duplicate-definition class that the llvm-lib FFI fixes had to patch ×4.
- **~400s per probe** (the stage2 self-compile builds a large closure).
- **Parallel-sync clobber**: a concurrent full-WC sync reverts edits within
  seconds, so instrument via **atomic cp-into-main-repo + immediate run** (the
  seed reads stdlib from the main repo relative to the seed binary, NOT CWD —
  a detached worktree is NOT read by native-build).
- **Session kill-monitor** SIGKILLs `simple run`/exec-mode processes (rc=9);
  reproduce via `native-build`, not `run`.

## Next steps (in order)

1. **[#128] Pin the drop point.** Instrument the string-literal lowering in
   **both** copies simultaneously — `50.mir/mir_data.spl:486` `emit_const_str`
   AND `mir/mir_data.spl` (+ the HIR→MIR literal path) — with an `eprint` of
   `value`/`value.len()`, via atomic cp + one `SIMPLE_BOOTSTRAP=1 native-build`
   run. Grep the output for `1.0.0-beta`:
   - arrives as `""` → HIR/MIR-gen or seed string-literal handling bug.
   - arrives intact → the drop is between MIR store and emit (re-check the
     `_bootstrap_mir_functions` round-trip / seed value handling).
2. **Fix the single site** found in (1). If MIR-gen/pure-Simple → fix in `.spl`
   and re-run the stage2 probe; strings should carry content and the driver
   should print its version/help.
3. **Re-gate**: once the stage2 driver is non-inert, run the full
   `bin/simple build bootstrap` 3-stage and the extended smoke matrix before any
   redeploy to `bin/release`.

## Landed this session (verified, on origin/main)

- `7984ab3` — llvm-lib value_map return-threading + operand `LocalId.id` key →
  emitted IR passes LLVM verification (was invalid).
- `4866213` — llvm-lib trivial-binary milestone: create_target_machine
  Triple/CPU/Features NUL-terminate + cpu `x86-64-v1`→`x86-64` + name
  NUL-terminate (all 4 FFI copies). `42` and `40+2` → running ELF64 returning 42.

## Out of scope for #79 (recorded, not on the critical path)

- llvm-lib runtime-builtin decls (`#129`) — needed only if pursuing llvm-lib
  self-host; deployed binary has no LLVM.
- Interpreter completeness (`#99`) and class-in-array mutation (`#112`) —
  interpreter-lane items; `#112` repro blocked by the exec-mode kill-monitor.
