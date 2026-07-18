# Project Scope: Un-stub multi-module HIR/MIR lowering in the self-hosted driver

**Status:** Proposed (scoping only — not started)
**Date:** 2026-06-25
**Domain:** compiler / driver
**Risk:** High (core pipeline; bootstrap depends on current stub behavior)
**Effort:** Large / multi-session; unbounded until the P0 inventory is done
**Related:** [[interp_aot_source_pipeline_stubbed_non_functional_2026-06-25]],
[[interp_typed_optional_nil_field_access_sigsegv_2026-06-25]]

## Problem

In multi-source compilation mode (`self.ctx.sources.len() > 0` — the real path
for compiling whole programs and the compiler itself), the self-hosted driver
produces **real HIR/MIR only for the bootstrap-entry source** and emits **empty
module shells for every other source**. Consequently, arbitrary multi-module
programs are not actually lowered, type-checked at body level, or code-generated
by the self-hosted compiler — they silently pass with empty output.

This is the root blocker behind several deferred items, including a real
`-c --target wasm32` for non-trivial programs and any narrowing-aware
compile-time check (e.g. the optional-field nil-access rule).

## Current state (exact locations)

1. **HIR stub** — `src/compiler/80.driver/driver.spl`, `lower_and_check_impl()`:
   - `sources.len() <= 0` branch (lines ~389–411): **real** lowering
     (`lower_module` + `resolve_methods` + `run_const_fold_pass` + `run_effect_pass`).
   - `sources.len() > 0` branch (lines ~412+): only `_driver_is_bootstrap_entry_source`
     gets `lowering.lower_module(...)`; every other module is built as an empty
     `HirModule(functions: {}, classes: {}, ...)` (lines ~432–449).
   - Reason, verbatim from the code (lines 426–428): *"Bootstrap stage1 cannot
     safely dereference the parsed frontend Module in HIR lowering yet; keep
     phase3 moving with an empty HIR shell while the frontend module
     representation is stabilized."*

2. **MIR stub** — `src/compiler/80.driver/driver_pipeline.spl`, `lower_to_mir()`:
   - `sources.len() > 0` branch (lines ~312+): only the bootstrap entry gets
     `direct_lowering.lower_module(...)`; non-entry sources get an empty
     `MirModule(functions: {}, ...)`.

3. **Frontend prerequisite (already fixed this session):** `parse_full_frontend`
   in `src/compiler/10.frontend/frontend.spl` previously returned nil (missing
   trailing `module` return); fixed and landed. Parse now produces real modules
   for all sources — only HIR/MIR remain stubbed.

## What un-stubbing exposes (known downstream bug chain)

Un-stubbing immediately surfaces an unbounded chain of interpreted-compiler bugs;
the ones already identified:

1. **Option.map on a present bare value** — the interpreter represents `Some(x)`
   as the bare value, with no Some-fallback for Option methods, so
   `fn_.return_type.map(...)` (`hir_lowering/_Items/declaration_lowering.spl`) errors
   "method 'map' not found on type 'Type'". Worked around at one callsite; others
   remain exposed.
2. **`resolve.spl` MethodResolver method orphaning** — two indent-0 free functions
   between the class fields and its `me` methods close the class early, absorbing
   methods 177+ into a free function → `resolve_module` fails on nil.
3. **Typed-optional nil field-access crash** — now guarded at runtime in the JIT
   (`d3a020c85f30`), but is reachable in real code once bodies lower.

This list is **not exhaustive** — it is whatever the stub has been hiding. The
true scope is unknown until P0 enumerates it.

## Separate-but-adjacent gap: HM type inference is dormant

Probing this session showed `HmInferContext.synthesize_expr` fires **0 times**
when checking a user file. Even with HIR un-stubbed, the Hindley-Milner inference
engine in `src/compiler/30.types/type_infer/` may not be wired into the check
pipeline over function bodies. Un-stubbing HIR is necessary but likely **not
sufficient** for narrowing-aware type analysis; wiring HM inference is a distinct
sub-task (P3). This needs verification early.

## Phased plan

- **P0 — Inventory (read-only + flag-gated).** Add a `SIMPLE_UNSTUB_HIR=1`-style
  flag that takes the real lowering branch for all sources. Run over a corpus
  (single-module, then small multi-module programs, then a compiler subdir).
  Catalog every failure with file + phase. Output: a concrete, bounded bug list.
  Do **not** fix anything yet.
- **P1 — Frontend Module stability.** Resolve the root reason cited in the stub
  comment (safe dereference of the parsed frontend Module in HIR lowering) so
  `lower_module` accepts arbitrary parsed modules. Likely the highest-leverage fix.
- **P2 — Downstream bugs.** Fix the enumerated chain (Option API fallback,
  `resolve.spl` orphaning, etc.) one at a time, each with a runnable guard test.
- **P3 — Type-check wiring (optional, only if the compile-time checks are wanted).**
  Verify/restore HM inference over bodies in the check pipeline. Prerequisite for
  the optional-field check (~40–283 sites; see related doc).
- **P4 — Remove the stub.** Delete both empty-shell branches. Gate removal behind:
  multi-module corpus green, full test suite non-regressive, **bootstrap Stage 3
  self-host still green** (the current bootstrap depends on the stub today).

## Risks

- **Bootstrap dependency.** Stage 2/3 self-host currently relies on the entry-only
  lowering. Un-stubbing can break the bootstrap; all work must be flag-gated until
  P4 and validated against a full bootstrap.
- **Unbounded fix chain.** Effort cannot be estimated past P0; minimal repros have
  historically misled (bugs are compilation-unit-dependent).
- **Two coupled subsystems.** HIR and MIR stubs must be lifted together to get
  end-to-end output; lifting one alone yields empty MIR or unused HIR.

## Acceptance criteria

1. A multi-module program produces non-empty HIR **and** MIR for all its modules.
2. `bin/simple -c <prog> --target wasm32 -o out.wat` emits a real (non-empty) WAT
   module for a real multi-function program (the original "fix wasm" goal).
3. Full test suite non-regressive; bootstrap Stage 3 self-host still green.
4. The stub branches are deleted, not flag-hidden.

## Open questions (resolve in P0)

- Is the frontend-Module-stability issue a single root fix or many per-node fixes?
- Is HM inference actually invoked anywhere in `check`/`build`, or fully dormant?
- Does the `sources.len() <= 0` branch (single-file) already lower fully and
  type-check, or is it also incomplete? (It calls the real passes, but HM did not
  fire — clarify what "real" covers there.)
