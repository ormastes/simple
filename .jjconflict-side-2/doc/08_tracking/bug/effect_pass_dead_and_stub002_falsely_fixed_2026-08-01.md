# Effect inference pass is dead code; STUB-002 falsely marked Fixed

**Date:** 2026-08-01
**Status:** RESOLVED 2026-08-02 — ruled DELETE, executed. See "Resolution" at
the end of this file.
**Severity:** P2 — no wrong compiler output today, but a tracked P1 requirement
is recorded as Fixed when it is not, and its guarding spec is false-green.
**Files:**
- `src/compiler/30.types/type_system/effect_pass.spl`
- `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:204`
- `test/02_integration/compiler/driver/effect_inference_wiring_spec.spl`
- `test/01_unit/compiler/type_system/effect_pass_spec.spl`
- `doc/02_requirements/language/features/eliminate_dummy_impls.md` (STUB-002)

## Summary

`run_effect_pass` has never executed on any build. Three independent defects
stack on top of each other, and each one alone would have hidden the others.

## Defect 1 — the pass body is unreachable (PROVED)

`effect_pass.spl` line 24 onward, at base `3487c07ce414`:

    fn run_effect_pass(modules: Dict<text, HirModule>) -> (Dict<text, HirModule>, [text]):
        # Skip effect inference in bootstrap (method calls crash in native binary)
        var empty_warnings: [text] = []
        return (modules, empty_warnings)

The return is **unconditional** — there is no env check, no bootstrap predicate,
nothing. The comment's "in bootstrap" framing is inaccurate. Lines 28-394 (367
lines: solver setup, fixed-point propagation, write-back, constraint validation)
are dead on every build. The function's docstring was placed *after* the return,
so even it was unreachable.

## Defect 2 — the pass is not wired into the main pipeline (PROVED)

STUB-002 records the fix as `run_effect_pass(self.ctx.hir_modules)`. The tree has
exactly one call site, `driver_hir_pipeline_lowering.spl:204`:

    val (updated_hir_boot, effect_warnings_boot) = run_effect_pass(bootstrap_hir_modules)

It passes `bootstrap_hir_modules`, and it sits inside the bootstrap-only branch
that returns `bootstrap_ctx` early. The non-bootstrap compilation path never
calls the pass at all. So even if Defect 1 were fixed, effect inference would
still not run for ordinary builds.

## Defect 3 — the guarding spec is vacuous (PROVED)

`effect_inference_wiring_spec.spl` is headed "Verifies that the effect inference
pass is actually wired into the driver" and carries `@req STUB-002`. Its entire
assertion is:

    var modules: Dict<text, HirModule> = {}
    val (result_modules, warnings) = run_effect_pass(modules)
    expect(warnings.len()).to_equal(0)
    expect(result_modules.keys().len()).to_equal(0)

An empty dict in, empty out. This passes identically against the early-return
stub and against a fully working pass, and it never touches the driver it claims
to verify. It cannot distinguish wired from unwired.

`effect_pass_spec.spl` is a placeholder that asserts a pending-reason string is
non-empty; it is a green no-op, not coverage.

## Consumer analysis — why this is not currently miscompiling anything

Enumerated repo-wide with `/usr/bin/grep` (not ugrep). `HirFunction.effects:
[Effect]` has these readers, and **every one is pure pass-through**:

| Site | Use |
|---|---|
| `35.semantics/resolve.spl:275` | `effects: func.effects` — copies field to rebuilt fn |
| `30.types/type_infer/traits.spl:81` | `effects: hir_fn.effects` — copies field |
| `30.types/type_infer/inference_control.spl:589` | puts effects into `HirTypeKind.Function(...)` |
| `30.types/type_infer/generalization.spl:163` | carries effects through instantiation |
| `20.hir/hir_lowering/async.spl:465` | binds `effects` in a pattern, body never uses it |

No site branches on, filters, compares, or tests the contents. Unification
(`30.types/type_infer/core.spl:113`) matches
`case (Function(p1, r1, _), Function(p2, r2, _))` — the effects slot is `_` and
is ignored; `bidir_phase1a/1b` `types_equal` do not carry effects at all. Every
other `HirTypeKind.Function` destructure in the tree uses `_` for that slot.

Two corrections to assumptions worth recording:

- `35.semantics/verification_checker.spl:95,104` reads `func.effects` but `func`
  is `FunctionInfo`, whose `effects` is `[text]` (line 56) — a **different type**
  populated from attributes. Same for `00.common/predicate.spl:118`,
  `10.frontend/core/aop.spl:457`, `00.common/compilation_context.spl:137`. These
  are not consumers of `HirFunction.effects`.
- The field is **not** empty at rest.
  `20.hir/hir_lowering/_Items/declaration_lowering.spl:418-421` seeds
  `Effect(kind: EffectKind.Async)` for `is_async` functions. So consumers are not
  reading default/garbage data — they read the annotation-derived seed, which is
  the coarse value the pass was meant to *refine* by call-graph propagation.

**Consequence:** turning the pass on today would change nothing observable. No
consumer inspects the value it would refine. It would only add a fixed-point
solve over every function to every build.

## Why this was not simply deleted

Repo policy says never leave unused code. Deleting was not taken unilaterally
because STUB-002 is a tracked **P1** requirement in
`doc/02_requirements/language/features/eliminate_dummy_impls.md` whose stated
intent is that this pass be wired. Deleting the implementation would silently
close a requirement by destroying its subject. That call belongs to the
requirement owner.

Also relevant to the decision: `effect_pass.spl` is the only in-tree consumer of
`00.common/effects_solver.spl` (`effectsolver_create` / `effectsolver_solve`).
Deleting the pass orphans the solver, which is still public API re-exported from
`00.common/__init__.spl:77`, alongside `effects_scanner.spl`,
`effects_cache.spl`, `effects_env.spl`, `effects_promises.spl` and
`effects_v1_simple.spl`. A delete must enumerate that whole family rather than
remove one file and leave the rest stranded.

## Recommendation (for the STUB-002 owner)

**Prefer delete.** Effect inference has no consumer, no test that exercises it,
and no dependent feature. Refining `HirFunction.effects` cannot affect codegen
until something reads it. Deleting `effect_pass.spl`, its single call site, the
`30.types/type_system/__init__.spl:51` re-export, both vacuous specs, and the
orphaned `effects_*` family removes ~400 lines from the pass plus the solver
subsystem, and lets STUB-002 close honestly as "withdrawn, not implemented".

**If instead it is to be implemented**, all three defects must be fixed together,
and the following must hold before it can be called done:
1. Move the call out of the bootstrap-only branch onto the main pipeline path.
2. Give at least one consumer a reason to read the field, otherwise the pass is
   still observationally dead.
3. Replace `effect_inference_wiring_spec.spl` with a non-vacuous spec: a module
   containing a sync function that calls an async function, asserting the sync
   function acquires `EffectKind.Async` by propagation. Show it RED against the
   current stub before making it GREEN.
4. Measure. This adds a fixed-point solve over every function to every build; the
   original disable comment blames "method calls crash in native binary", which
   is unverified and must be re-tested rather than assumed stale.

## What this change does

Nothing behavioural. It corrects the inaccurate comment at the disable site,
moves the docstring above the early return so it is attached to the function,
reopens STUB-002 with the evidence, and files this report. The early return is
left in place deliberately — removing it is the owner's call, and doing it
blindly would enable an unmeasured, unexercised pass.

## Not reproduced / retracted

An earlier reading of this report suspected the write-back's
`HirModule(... types: [])` (effect_pass.spl:128) of dropping module type data.
Retracted: `HirModule.types` is `[text]` (`20.hir/hir_types.spl:45`), is
constructed empty at every HIR construction site, and has no reader. The
`module.types.keys()` uses in the VHDL and C backends are `MirModule`, a
different type. `types: []` is therefore harmless and was left unchanged.

## Resolution — 2026-08-02: DELETED

The delete-vs-implement ruling was taken and executed. Recorded here so the next
reader does not re-derive it.

### Reachability re-established by MEASUREMENT, not reading

The earlier finding was based on reading the arm. It was re-proved by execution,
with a live positive control, because reading an arm alone produced wrong
predictions twice elsewhere on 2026-08-01:

- a probe print placed immediately BEFORE the early return **fired**
- a probe print placed immediately AFTER it, as the first statement of the
  claimed-dead region, **never fired**

Both from one `bin/simple run` driver calling `run_effect_pass({})`. The positive
half is what makes it evidence: the function is entered, the return is reached,
and nothing past it executes. 356 lines, unreachable.

### Caller enumeration, per symbol, before deleting

Required because deleting a reimplementation REROUTES its callers rather than
deduplicating them. Enumerated with `/usr/bin/grep` (ugrep is the interactive
default and was not used):

| Symbol | Referents outside `effect_pass.spl` |
|---|---|
| `run_effect_pass` | facade re-export, driver import + sole call site, `stubs.rs` keep-list, 2 duplicate spec files — all removed together |
| `build_function_effect_info` | none |
| `BodyScanResult` | none |
| `empty_scan` | none |
| `merge_scans` | none |
| `scan_expr` / `scan_block` / `scan_stmt` | **no callers.** The `40.mono/monomorphize_integration.spl` and `70.backend/backend/interpreter.spl` hits are `me` methods on a different class, invoked as `self.scan_expr(...)` — a bare-name collision, not a shared helper |

Nothing rerouted: every referent was deleted with the definition.

### What was deleted

- `src/compiler/30.types/type_system/effect_pass.spl`
- its facade re-export in `30.types/type_system/__init__.spl`
- its import and sole call site in `80.driver/driver_hir_pipeline_lowering.spl`
- `"run_effect_pass"` from the `EXTRA_KEEP` list in
  `src/compiler_rust/compiler/src/linker/native_binary/stubs.rs`
- both copies of the vacuous wiring spec (`test/02_integration/...` and the
  legacy `test/integration/...` duplicate) and both copies of the placeholder
  `effect_pass_spec.spl`, plus their stale `summary.txt` artifacts

The call site removal is semantics-preserving and provably so: the pass was the
identity function, so `updated_hir_boot` was `bootstrap_hir_modules`. The second
binding, `effect_warnings_boot`, was never read.

### What was NOT deleted, and why

The `00.common/effects*.spl` family (`effects.spl`, `effects_solver.spl`,
`effects_cache.spl`, `effects_scanner.spl`, `effects_env.spl`,
`effects_promises.spl`, `effects_phase3a.spl`, `effects_v1_simple.spl`, ~931
lines) is now consumer-free, but is deliberately left for a separate measured
lane. `00.common/__init__.spl` re-exports **the same names** — `EffectTag`,
`EffectEnv`, `EffectStats`, `FunctionEffectInfo` — from FOUR different modules
(lines 62, 65, 68, 80). Removing any one of them reroutes that name to whichever
export survives. Measured: no file imports those names through the
`compiler.common` facade today, so the reroute is currently unobservable — which
is the argument for doing it as its own change with its own controls, not for
bundling it blind into this one.

### Verification performed (and one trap caught)

No bootstrap was run; another lane owns that. `bin/simple check` and
`bin/simple lint` both refuse on the seed ("pure-Simple tool unavailable;
refusing Rust fallback"), so the compile-level check is NOT available here and is
NOT claimed. What was verified:

- **Negative control:** a driver that IMPORTS AND CALLS `run_effect_pass` runs
  and prints against the pristine tree (exit 0) and fails against the edited tree
  (exit 1, marker absent). The symbol is genuinely gone.
- **Positive control:** a driver importing the type_system facade, the edited
  driver module, the edited `declaration_lowering.spl`, `effects.spl` and
  `effects_scanner.spl` loads with **zero** unresolved-import warnings, identical
  to pristine.

**Trap caught, recorded because it nearly produced a false PROVED:** an
unresolved `use` is only a `[WARN] Failed to load imported types` — the program
still runs and **exits 0**. So an import-only probe scored by exit code is
fail-open and cannot tell a deleted module from a present one. The controls above
score a CALL and a warning count instead. The `stubs.rs` edit removes one element
from a `&[&str]` array and is not compile-verified here.
