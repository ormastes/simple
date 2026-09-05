# gen-lean regeneration pipeline broken (multi-layer drift)

Status: FIXED 2026-06-11 — all layers repaired, 4 lean_* spec suites green (27/27)

**Date:** 2026-06-11
**Severity:** Medium (verification automation gap — committed Lean proofs cannot be
machine-compared against their regenerator sources; manual L4 audit confirmed
AsyncEffectInference is currently in sync)
**Found by:** Wave-3a task L4 (hardening plan 2026-06-11)

## Problem

`bin/simple gen-lean compare` fails before comparing anything. The regeneration
modules under `src/compiler_rust/lib/std/src/verification/regenerate/` had never
been runnable in the current interpreter; failures peel like an onion:

1. **(FIXED 2026-06-11)** `use verification.lean.codegen as codegen` — module
   aliasing is not implemented in the interpreter (known limitation, see
   `test/01_unit/compiler/parser/module_alias_spec.spl`). All 14 regenerate
   scripts AND the whole `verification/lean/*.spl` library (18 files, ~22
   aliases) used alias imports. Sweep applied: direct member imports
   (`use mod.{a, b}`) + prefix strip.
2. **(FIXED 2026-06-11)** `var gen = ...` — `gen` is a reserved keyword; the
   binding silently failed to resolve ("variable `gen` not found"). Renamed to
   `lgen` in 7 scripts.
3. **(FIXED 2026-06-11)** `semantic: method 'add_param' not found on type 'LeanFunction'`
   — `build_function` in the codegen library calls an API that no longer exists
   on `LeanFunction`. Genuine API drift inside `verification/lean/` that was
   never caught because the pipeline was already unrunnable at layer 1.
   Fixed by restoring `add_param` as a `me` method on `LeanFunction` and
   wiring `LeanCodegenOptions.new()` as a static factory.

## Also discovered (pre-existing, NOT caused by the sweep — verified by
restoring FETCH_HEAD copies and re-running)

- `lean_basic_spec.spl` 4/4 (green before and after)
- `lean_codegen_spec.spl` 4/4 (fixed: `gen` reserved keyword → `cgen`)
- `lean_block_integration_spec.spl` 10/10 (fixed: `gen` keyword + import emission in `emit()`)
- `lean_workflow_spec.spl` 9/9 (fixed: multiple issues — see below)

## Additional fixes applied 2026-06-11 (lean_workflow_spec)

- `obligations.spl`: `io.fs` stub → `std.nogc_sync_mut.io`; `Dict<text,bool>` false-as-nil
  bug → `Dict<text,text>` with "match"/"mismatch"; `translate_contract_expr` wrong import;
  `clause.condition` → `clause.expr`; Python-style `.append()` → `list + [item]`;
  `None` → `nil`; `ObligationCategory` variants renamed; `to_lean_theorem()` uses
  `build_theorem()` (same-module free fn avoids cross-module me-method loss);
  `Option<text> is not nil` bug workaround: use `.to_text() != "nil"`.
- `checker.spl`: `True`/`False` → `true`/`false`; `.append()` → `list + [item]`;
  `ProofStatus` class renamed `ProofStatusReport` (conflicts with enum); `None` → `nil`;
  nil guard on `_rt_process_run` return with static sorry-scan fallback for no-Lean envs.
- `codegen_part1.spl`: `build_theorem()` uses direct constructor (avoids me-method
  cross-module mutation loss); `proof_text()` uses `match Some(p)` pattern.
- `__init__.spl`: `io.fs` stub → `std.nogc_sync_mut.io`; `Dict<text,bool>` → text values;
  `rt_dir_create_all` (unimplemented) → `shell("mkdir -p ...")`.
- `lean_workflow_spec.spl`: chained method call split to intermediate var; `io.fs` imports
  fixed; `temp_path` aligned to actual written path via `written[0]`.
- `tensor_dimensions.spl`: `val lgen` → `var lgen` (first assignment needs `var`).
- `runner.spl`: format string `"Unproven:"` → `"Unproven (sorry):"`.

## Status

All 15 regeneration layers complete (MISMATCH results are expected — Lean files on disk
predate regenerator). All 4 lean_* spec suites: 27/27 green. No lint errors on touched files.
