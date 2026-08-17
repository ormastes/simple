# `iso` MIR lowering: erasure fixes two use-after-move cases but regresses the non-`iso` control

- **ID:** iso_mir_lowering_erasure_fixes_two_cases_regresses_non_iso_control_2026-08-08
- **Date:** 2026-08-08
> **RETRACTED 2026-08-08 — THIS DOC'S CENTRAL MEASUREMENT IS WRONG.** The patch
> below is CORRECT and landed in `7a8115c6091`. The spec is **4/4**, not 2/4, and
> the non-`iso` control never regressed. The 2/4 table was a harness artifact:
> `bin/simple test` degrades silently near its 800-module ceiling and still prints
> a well-formed `Results:` line with wrong verdicts. Re-measured with
> `SIMPLE_MODULE_LIMIT=0` (`src/compiler_rust/compiler/src/memory_guard.rs:55`):
> baseline 1/4, patched **4/4**. Read the "Retraction" section at the end before
> anything else here.

- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  trades one passing test for two; see the table)
- **Severity:** medium — blocks
  `borrow_check_bypassed_on_interpret_path_2026-08-08`, which names this as its
  prerequisite.

## The gap

`lower_type` (`src/compiler/50.mir/_MirLowering/function_lowering.spl:641`) has no
`HirTypeKind.Isolated` arm, so every `iso`-typed local falls to the wildcard and
dies with `unsupported MIR type kind [wildcard-arm]`. Three such errors are
emitted for the 3-line repro (`val x: iso i64 = 5; val y = x; val z = x`), one
per `iso` local.

Attribution correction: those errors come from **`MirLowering.lower_module`**, not
from HIR lowering. `borrow_check_bypassed_on_interpret_path_2026-08-08.md` says
"HIR lowering ... emits 3 errors"; HIR lowering passes cleanly both before and
after. The MIR type-lowering pass is the one that fails.

## The candidate patch

In `lower_type`'s match, before the `case _:` wildcard (which currently sits at
~786 behind a committed `TEMP-PROBE`):

```
case HirTypeKind.Isolated(inner):
    self.lower_type(inner)
```

Rationale for erasure over a distinct MIR representation: isolation is an
ownership/aliasing property, not a runtime one.
`mir_hir_type_is_isolated` (`mir_lowering_stmts.spl:89`) already reads
`HirTypeKind.Isolated` off the HIR-type side table to choose `emit_move` over
`emit_copy`, so the Move fact reaches the borrow checker entirely at the HIR-type
layer and never needs its own `MirType`.

## Measured result — the reason it was NOT landed

`bin/simple test test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl
--no-cache --no-cover-check`, run at origin and again with the patch, on the same
tree minutes apart:

| test | baseline (origin) | with patch |
|------|-------------------|------------|
| reports a use-after-move error for a moved-then-reused `iso` local | FAIL | **PASS** |
| reports a use-after-move error for a moved `iso` local used as a call argument (`print x`) | FAIL | **PASS** |
| reports no error for the same shape when the moved source is never reused | FAIL | FAIL |
| reports no error for the identical shape **without** `iso` (non-`iso` control) | **PASS** | **FAIL** |
| **totals** | **1/4** | **2/4** |

Net +1, but it converts a passing control into a failing one. **The non-`iso`
control regressing is the important signal:** it means erasure is making ordinary
non-`iso` bindings look moved to the borrow checker. The remaining `iso` failure
("no error when the moved source is never reused") is the same over-firing
symptom on the `iso` side, so both open failures are one defect: **the checker
now reports use-after-move where no reuse occurred.**

This directly contradicts the reasoning that erasure is safe because "case 1 and
case 3 pass simultaneously". They do not — measured independently, they do not
both pass.

`borrow_check_spec.spl` stays 11/11 with and without the patch. That spec
hand-builds MIR and never calls `lower_type`, so it cannot observe this either
way — it is not evidence of safety here.

## What the next lane needs to do

The `Isolated` arm is necessary but not sufficient. Erasing `iso T` to `T` means
the MIR type no longer distinguishes the two, so whatever consumes the Move fact
must be keyed on the HIR-type side table alone — and something downstream is
evidently keying on the lowered type, or is treating an erased binding as moved
unconditionally. Find the consumer that changed behaviour when the wildcard-fatal
stopped firing, rather than adjusting the arm.

Do NOT make this spec green by weakening the control. Per
`.claude/rules/testing.md`, a correct spec that fails stays RED and gets filed —
the non-`iso` control is asserting exactly the right thing.

## Reproduction

```
# baseline
git cat-file -p origin/main:src/compiler/50.mir/_MirLowering/function_lowering.spl \
  > src/compiler/50.mir/_MirLowering/function_lowering.spl
bin/simple test test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl \
  --no-cache --no-cover-check      # -> Results: 4 total, 1 passed, 3 failed

# with the patch applied -> Results: 4 total, 2 passed, 2 failed
```

Only the final `Results:` line and the exit code are authoritative; the output is
flooded with lint noise. Never take `$?` from a pipe.

## Note on the spec's own header

The spec claims 4/4 in its header and has never been 4/4 in this measurement
(1/4 at origin). The header is stale. Do not edit it to match a number without
also stating which cases are genuinely broken — that would convert a documented
defect into a hidden one.

## Related

- `doc/08_tracking/bug/borrow_check_bypassed_on_interpret_path_2026-08-08.md` —
  names this as its blocking prerequisite; its "HIR lowering emits 3 errors"
  attribution is corrected above.
- `doc/08_tracking/bug/native_build_self_hosted_mir_infer_type_crash_2026-07-30.md`
  — a `native-build` repro of this gap is confounded by that separate
  module-level-global `HirTypeKind::Infer` crash, which fires identically on a
  non-`iso` control. Use the in-process spec path, not `native-build`, as the
  oracle for `iso`.


---

## Retraction (2026-08-08)

**What this doc got wrong:** it reported the `Isolated` erasure patch scoring 2/4
and *regressing* the non-`iso` control, and concluded the borrow checker
over-fires on bindings with no reuse. All of that is false.

**The cause of the false reading:** `bin/simple test` was silently degrading near
its 800-module ceiling. This spec's transitive module load exceeds that limit, and
the runner **still emitted a well-formed `Results:` line while producing wrong
verdicts.** That is a false RED that looks exactly like a real regression — there
is no crash, no warning, and the output is structurally perfect.

**Re-measured with `SIMPLE_MODULE_LIMIT=0`:**

| run | result |
|-----|--------|
| baseline (no patch), limit lifted | `4 total, 1 passed, 3 failed` |
| patched, limit lifted | `4 total, 4 passed, 0 failed` |

Baseline still reproduces at 1/4, so the defect and the fix were both real. Only
the intermediate 2/4 was noise.

**Why the non-`iso` control could never have regressed:** `case
HirTypeKind.Isolated` is structurally unreachable for `val x: i64 = 5` — a
non-`iso` binding cannot produce an `Isolated` HIR type, so the arm cannot affect
it. Code inspection alone should have refuted the measurement; I trusted the
number over the structure.

Regressions, all with the limit lifted: `borrow_check_spec` 11/11,
`iso_move_pipeline_spec` 4/4, `iso_move_sites_spec` 2/2.

**The transferable lesson, which outlives this bug:** any in-process
compiler-spec oracle in this tree needs `SIMPLE_MODULE_LIMIT=0`. Without it the
runner can return a confident, well-formed, WRONG verdict rather than failing
loudly. The repro command originally given in this doc is unsound as written for
exactly that reason. When a measurement contradicts the structure of the code,
suspect the harness first.
