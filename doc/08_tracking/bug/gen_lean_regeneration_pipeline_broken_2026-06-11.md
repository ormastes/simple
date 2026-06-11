# gen-lean regeneration pipeline broken (multi-layer drift)

Status: open (partially fixed 2026-06-11 — first two layers repaired, third blocks)

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
3. **(BLOCKS)** `semantic: method 'add_param' not found on type 'LeanFunction'`
   — `build_function` in the codegen library calls an API that no longer exists
   on `LeanFunction`. Genuine API drift inside `verification/lean/` that was
   never caught because the pipeline was already unrunnable at layer 1.

## Also discovered (pre-existing, NOT caused by the sweep — verified by
restoring FETCH_HEAD copies and re-running)

- `test/00_formal_verification/compiler/lean_block_integration_spec.spl`: 2/2 fail
- `test/00_formal_verification/compiler/lean_codegen_spec.spl`: 2/4 fail
- `test/00_formal_verification/compiler/lean_workflow_spec.spl`: parse error in
  `src/compiler_rust/lib/std/src/verification/proofs/obligations.spl`
  ("expected identifier, found Invariant" — likely another reserved-word/grammar
  issue)
- `lean_basic_spec.spl` 4/4 passes (before and after sweep).
- The per-suite `summary.txt` files claim all-green; they are stale.

## Next steps

- Fix `LeanFunction.add_param` drift (align build_function with the current
  LeanFunction API), then continue peeling until `gen-lean compare` completes.
- Fix `obligations.spl` parse (reserved identifier `Invariant`?).
- Re-run the four lean_* spec suites for real and refresh summary.txt.
- Until then: drift checks for auto-generated Lean (AsyncEffectInference) must
  be done manually (last manual audit 2026-06-11: in sync).
