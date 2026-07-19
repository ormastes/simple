# HOSTED native `.?` / if-val Option unwrap leaks the Some tag instead of the payload

**Date:** 2026-07-19
**Status:** OPEN — origin-base regression, reproduces on pristine origin, not a
local-branch defect.
**Severity:** P1 — silent miscompile (wrong value, no diagnostic) on a
first-class language construct.
**Component:** compiler codegen — Option/`.?` (try-op) + `if val` binding
lowering, **hosted** native-build (`x86_64-unknown-linux-gnu`, seed native-build
path). Distinct locus from the baremetal class
([baremetal_option_field_unwrap_faults_class_2026-07-18](baremetal_option_field_unwrap_faults_class_2026-07-18.md)),
same "Some payload not extracted" family.

## Symptom

```simple
fn main() -> i64:
    val x: i64? = 7
    if val v = x.?:
        return v      # expected 7
    return 0
```

Native-built with the seed on `x86_64-unknown-linux-gnu`, `main()` returns **84**,
not 7. The `if val` **Some-branch is taken** (it does not fall through to
`return 0`), so the Option is correctly recognized as present — but the bound
value `v` is the tagged/boxed `Some` representation, not the unwrapped payload
`7`. i.e. payload extraction after the try-op unwrap is wrong.

## Root cause (bisected)

Introduced by origin commit **`d71449a36dc fix(native): restore canonical Option
ABI`** (first present at base `eb3a695b185`). Evidence:

- The **same** local fix batch produced optnil=**7** at base `874687bc7bf`
  (pre-`d71449a`) and optnil=**84** at base `eb3a695b185` (post-`d71449a`). The
  batch is byte-identical across both bases, so it is ruled out as the cause.
- At `eb3a695b185`, reverting every batch-touched `.?`-lowering-surface file
  (`switch_operators_calls.spl`, `convert_nodes.spl`, `method_calls_literals.spl`)
  to origin-clean leaves optnil=**84** (Stage A + Stage B file-swap tests on the
  already-built seed).
- Origin drift `eb3a695b185..4e8efcf0e53` (28 commits) contains **no `.?` /
  Option-ABI fix** — the regression is still live on current origin.

`d71449a` reworked the Option representation across
`method_calls_literals.spl`, `switch_operators_calls.spl`, `expr_dispatch.spl`,
`function_lowering.spl`, `mir_lowering_stmts.spl`, `core_enum.spl`,
`runtime_native.c`. Origin's own repro
(`native_option_uniform_tagged_abi_repro.spl`) exercises `unwrap_or` and
`through_try` (which *returns* an `Option`), but **not** the
`if val v = x.?: return v` shape that unwraps to a bare payload — that shape is
the blind spot that regressed.

## Related / class

Same family as the hosted enum-payload box/unbox findings (`a4e7` audit:
`box_enum_payload_if_needed` gates on arg type not declared `Option<T>` element
type; `rt_enum_payload` extract Unbox is shared) and the baremetal Option-unwrap
class. This is a recurring class — see
[feedback_recurring_problem_team_analysis_and_tests] — and needs a codegen
root-fix plus box/unbox + Option-binding regression tests, not a per-shape patch.

## Repro

`NATIVE_SMOKE_CASES=optnil scripts/check/native-smoke-matrix.shs` (case
`optnil|i64? .? unwrap|...|7`) — currently marked xfail against this bug until
the origin `.?` payload-extraction path is fixed.
