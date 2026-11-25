# Windows self-hosted compiler overflows the 1 MiB default stack lowering a deep `or` chain

- **Date:** 2026-11-24  **Lane:** rb5 bootstrap, release/1.0.0 pin `0285176e3a7b`, x86_64-pc-windows-msvc
- **Symptom:** Phase 3 -> Phase 3 (P3 compiling the bootstrap CLI) ended `go-to-end: 115 failure(s) (mir=115)`:
  three MIR shard workers died (`CRASH in the MIR shard pool`, 114 modules swept), attributed to
  `lib.common.process.observation_v4`, `app.build.targets.action_identity`,
  `compiler.driver.cache.native_build_environment_identity`.
- **Repro (in-process, cdb):** `native-build --threads 1 --emit-object src/lib/common/process/observation_v4.spl`
  under cdb -> `Stack overflow - code c00000fd`; frames resolve (lld /MAP) to
  `MirLowering.lower_expr_impl+0x1a6` / `MirLowering.lower_expr+0xd83` while lowering statement 2 of
  `freeze_process_observation_cleanup_receipt_v4` (`observation_v4.spl:1023`), a ~40-term `or` chain.
- **Cause:** `msvc.spl build_args` emits no `/STACK:`, so lld-link's 1 MiB default applies
  (`SizeOfStackReserve: 1048576` on both P2 and P3). The seed-built P2 lowers the same function; the
  P2-built P3 has larger frames and overflows. Recursive `lower_expr` depth is proportional to chain length.
- **Workaround (W51):** relink P3 with `/STACK:67108864` (same objects); the module lowers in 17 s.
- **Fix:** `build_args` adds `/STACK:67108864` unless `extra_args` already carries one;
  `PeImagePolicy.default()` stack reserve raised to 64 MiB for the internal COFF linker.
- **Still open:** `lower_expr` recursion on long binary-operator chains is unbounded in the source;
  an iterative lowering of left-assoc chains would remove the dependence on stack size entirely.
- **Open gaps (review 2026-11-24, closed 2026-11-25):** the `extra_args` override check matched `/STACK:` exact-case only (lld-link also
  accepts `/stack:`, `-STACK:`, `-stack:`), and the windows-gnu lane (`native_all_support.spl` `NATIVE_MINGW_STACK_RESERVE_BYTES`) still
  defaulted to 8 MiB instead of 64 MiB. Both remaining linker parity gaps are closed below.

## Fix (2026-11-24, lowering side)

- **Root cause in the source:** `parse_or`/`parse_and` (`src/compiler/10.frontend/core/parser_expr.spl`) build
  `a or b or c` LEFT-associated, `Or(Or(a, b), c)` (`left = expr_binary(op, left, right)`); the HIR keeps that
  shape (`expression_core.spl:1513`) and `combine_pattern_conditions` builds match-guard chains the same way.
  `lower_binary_expr`'s `case And | Or:` arm recursed on `left` through `lower_cond_expr -> lower_cond_operand ->
  lower_expr -> lower_expr_impl -> lower_binary_expr`, one frame group per operand, with `lower_expr_impl`'s
  frame being the largest in the compiler -- so stack use grew linearly in chain length.
- **Change:** the arm now walks the same-operator left spine into a leaf list (stopping at a different operator or
  a non-`Binary` node) and `MirLowering.lower_logical_chain_v1(op, leaves)` lowers the leaves in a `while` loop.
  Iteration i emits exactly the MIR the recursion emitted for node `(l0 .. l(i-1)) op li`, with the accumulated
  Bool standing in for the recursively lowered left operand: own `logic_rhs`/`logic_short`/`logic_merge` blocks,
  own entry-alloca merge slot, `terminate_if` on the accumulator, `lower_cond_expr` on the leaf, Bool->i64 zext,
  store, merge load, `!= 0` Bool normalization. The MC/DC mask range per level is `[ordinal before l0, ordinal
  after l(i-1))`, the same pair the recursion computed because every node's left operand is the prefix rooted at
  `l0` and neither compound nodes nor `emit_mcdc_mask_range` advance the ordinal. Only the left spine is
  flattened; a parenthesised right-nested operand keeps its own node and mask range. Recursion depth is now
  independent of chain length; the 64 MiB `/STACK:` reserve from PR #11186 stays as defence in depth.
- **Not changed:** arithmetic/comparison chains (`case _:` arm) still recurse once per operand. That arm is not
  the same shape -- each node's result feeds Optional-payload, unit, erased-operand and enum-equality dispatch
  that reads both the HIR operand and its local -- so it was left alone; a 40-term `+` chain would need a
  separate change if it ever shows up as a real overflow.
- **Companion:** `mir_lower_trace_enabled()` (`_MirLowering/module_lowering.spl`) no longer treats
  `SIMPLE_COMPILER_PHASE_PROFILE=1` as a trace request. The bootstrap script defaults that switch to 1 on the
  Stage 4 build and under `--diagnostics test`, so every lane log carried a `[mir-lower] lower_function:*` line
  per function and statement (110+ MB, 2.1M lines in one rb5 build). `SIMPLE_COMPILER_TRACE=1` /
  `SIMPLE_BOOTSTRAP_DIAG=1` (what `--diagnostics debug` sets) behave as before; crash attribution from the last
  `lower_function:*` line now needs one of those two.
- **Guard:** `test/01_unit/compiler/driver/logic_operand_condition_position_lower_cond_expr_spec.spl` -- source
  shape of the arm and helper, runtime `or`/`and`/mixed chains with side-effecting operands pinning evaluation
  order and short-circuit, and a pure-Simple `MirLowering` run over a 60-term `or` chain asserting 59
  `logic_merge`/`logic_short`/`logic_rhs` blocks for the function.

## Fix (2026-11-25, remaining linker parity)

- **MSVC/lld-link stack override detection (`src/compiler/70.backend/linker/msvc.spl`):** `MsvcConfig.build_args`
  now normalizes `extra_args` entries with `arg.to_upper()` and checks both `/STACK:` and `-STACK:` prefixes
  (covering `/STACK:`, `/stack:`, `-STACK:`, `-stack:` case-insensitively) before appending the default
  `/STACK:{MSVC_DEFAULT_STACK_RESERVE}` (`67108864`).
- **Windows GNU/MinGW stack reserve parity (`src/compiler/70.backend/linker/_LinkerWrapper/native_all_support.spl`):**
  `NATIVE_MINGW_STACK_RESERVE_BYTES` raised from `8388608` (8 MiB) to `67108864` (64 MiB) in PR #11421, matching
  `PeImagePolicy.default()` (`0x4000000`) and `MSVC_DEFAULT_STACK_RESERVE`; `native_mingw_stack_reserve_args`
  now also checks case-insensitively (`flag.to_lower()`) for `--stack`, `--stack,`, `--stack=`, `-Wl,--stack`, and
  comma-separated `-Wl,...,--stack,...` overrides so explicit caller settings always suppress the default.
- **Guards:** `test/01_unit/compiler/linker/windows_mingw_stack_reserve_spec.spl`,
  `test/01_unit/compiler/linker/windows_mingw_p3_parity_spec.spl`, and
  `test/01_unit/compiler/backend/msvc_linker_candidate_spec.spl`.
