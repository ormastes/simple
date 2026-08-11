# iso/borrow-check unreachable from the interpret pipeline (`bin/simple test`)

- Status: open, scoped (investigated, deliberately NOT wired in)
- Related: `reference_borrow_check_runs_only_in_aot_pipeline` (memory),
  `src/compiler/50.mir/_MirLowering/function_lowering.spl` iso MIR-lowering
  prerequisite fix (commit `7a8115c60913ab30e3e07adba0b4bc53845aea50`, landed
  earlier 2026-08-08 — that fix is correct and orthogonal to this gap)

## Symptom

`bin/simple test` (the default fast path, runs the interpreter) never flags
`iso`/isolated-ownership violations. The same source only gets a borrow error
under `bin/simple build bootstrap` / `native-build` (AOT pipeline).

## Root cause (confirmed by reading the driver, not guessed)

This is a **structural gap**, not an oversight of a missing function call.

- `CompilerDriver.borrow_check()` (`src/compiler/80.driver/driver_pipeline_passes.spl:11-20`)
  iterates `self.ctx.mir_modules` and calls `check_mir_module(...)`
  (`src/compiler/55.borrow/borrow_check/mod.spl:357`), a single whole-module
  NLL/borrow analysis over **MIR**. There is no iso-only or cheap subset entry
  point — `check_mir_module` is the only entry, and it runs full NLL analysis,
  not a scoped "iso-transfer only" check.
- `self.ctx.mir_modules` is populated **only** by `CompilerDriver.lower_to_mir()`
  (`src/compiler/80.driver/driver_pipeline_lowering.spl:148`), a full,
  independent lowering pass with its own error surface, bootstrap-mode
  branches, and target-context handling.
- The interpret path (`CompilerDriver.interpret_pipeline()`,
  `src/compiler/80.driver/driver.spl:69-112`) never calls `lower_to_mir()`.
  It runs directly off `self.ctx.hir_modules` via
  `InterpreterBackendImpl.interpret_hir_module(hir_module)` — HIR in, no MIR
  representation ever constructed. `driver_orchestration.spl:185-187` returns
  `self.interpret()` straight out of phase 5, entirely bypassing the
  `borrow_check()` call that AOT makes at `driver_aot_pipeline.spl:97-102` /
  `driver_pipeline_execution.spl:21` / `driver_orchestration.spl:238` (AOT/VHDL
  paths only).

So "wire it in" is not `+1` call — it requires first running MIR lowering
(`lower_to_mir()`) unconditionally inside the interpret pipeline, then running
the **general** borrow checker (not an iso-scoped one) over the result.

## Why that's not a safe drive-by change

1. **Perf**: `lower_to_mir()` is a full second lowering pass (parallel to HIR
   interpretation, not reused by it). Per CLAUDE.md, `bin/simple test` is the
   default fast path — unconditionally adding a full MIR-lowering + NLL pass to
   every test invocation is a real latency/cost regression, not a free check.
2. **Blast radius**: `check_mir_module` runs the *general* NLL borrow checker,
   not an iso-specific rule. Turning it on globally would surface every
   existing borrow-check finding (many, per memory: `iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`,
   `iso_use_after_move_invisible_as_call_argument_2026-08-07.md`, and other
   open NLL/iso edge-case bugs referenced inline in
   `src/compiler/55.borrow/borrow_check/mod.spl:221-267`) on top of whatever
   MIR-lowering-only errors appear for code that today only ever goes through
   HIR interpretation. This risks breaking large amounts of currently-green
   `bin/simple test` output for reasons unrelated to the specific iso bug this
   was meant to catch.
3. **No cheap subset exists today**: there is no "iso-ownership-violations-only"
   entry point in `borrow_check/mod.spl` to scope the check to just the
   originally-fixed class of bug — building one is itself new-feature work,
   not a wiring fix.

## What the real fix requires (future work, not done here)

- Add a narrow, iso-specific check function in
  `src/compiler/55.borrow/borrow_check/mod.spl` (or a new sibling module) that
  only flags isolated-ownership transfer/use-after-move violations, callable
  without pulling in the full general NLL pass.
- Decide whether it runs on HIR directly (avoiding `lower_to_mir()` entirely —
  preferred, since it avoids both the perf and MIR-only-error blast radius
  above) or on MIR gated behind an opt-in flag (e.g.
  `--iso-check` / `SIMPLE_ISO_CHECK=1`) so it never silently changes the
  default `bin/simple test` fast path.
- Add before/after regression coverage: a fixture with a deliberate iso
  violation (must newly fail) plus a broad interpret-mode smoke run (must stay
  green) before flipping any default-on switch.

## Scope of this note

Investigated only — no source changes made beyond this doc. The MIR-lowering
prerequisite fix for `iso` (commit `7a8115c60913ab30e3e07adba0b4bc53845aea50`)
stands on its own and is unaffected by this gap; it fixes AOT/native-build's
iso MIR lowering, which is the path where `borrow_check()` is actually wired
today.
