# Bug: backend_optimization_*_for_budget_with_facts does not gate on required optimizer facts (8 failures)

- **Status:** open
- **Filed:** 2026-07-20
- **Affected spec:** `test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl`
- **Command:**
  `SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl --no-session-daemon`
- **Result:** `22 examples, 8 failures` (after fixing an unrelated `.?` truthiness bug in the
  same file at line 34 — see commit note below; 14 pass, 8 remain genuinely broken)

## Symptom (representative failures)

```
✗ gates backend recommendation plans on required optimizer facts
    expected false to equal true
✗ gates Simple loop unroll on canonical trip-count and budget facts
    expected call result to be truthy, got false
✗ gates Simple predicate promotion on candidate and safety facts
    expected call result to be truthy, got false
✗ gates Simple strength reduction on candidate and induction facts
    expected call result to be truthy, got false
✗ gates Simple scalar cleanup on SSA and alias facts
    expected call result to be truthy, got false
✗ keeps LLVM alloca shaping behind reassignment and backend facts
    expected false to equal true
✗ gates Simple auto-vectorization on candidate and alias facts
    expected call result to be truthy, got false
✗ gates Simple hot-call inlining on profile and budget facts
    expected call result to be truthy, got false
```

## Root cause (hypothesis, not confirmed — no src edit attempted)

Each failing `it` block calls
`backend_optimization_plan_for_budget_with_facts(backend, budget, facts_list)`
with a facts list missing one required fact, then loops
`plan.skipped_decisions` looking for a decision whose `stable_name` matches the
recommendation and whose `reason` explains the missing fact (e.g.
`"missing ssa.var_transform"`, `"missing unroll_budget"`,
`"missing predicate_safe"`, `"missing induction_safe"`,
`"missing alias_stable"`, `"missing inline_budget"`, `"missing
var.reassignment"` / `"missing escape.analyzed"`), setting a `found_x` flag
to `true` inside the loop.

The identical `var found_x = false; for decision in ...: if cond: found_x =
true; expect(found_x).to_equal(true)` idiom is used and PASSES in two other
`it` blocks in this same file ("explains skipped backend recommendations by
backend and compile budget" at line 150, "builds applied and skipped
recommendation plans in one decision pass" at line 163) — both of which call
the **non-facts** variant `backend_optimization_decisions_for_budget` /
`backend_optimization_plan_for_budget`. This rules out an interpreter
for-loop/closure-mutation bug (a known landmine class) as the cause, since the
identical loop-and-flag idiom works fine elsewhere in the same file — the
divergence is isolated to the `_with_facts` variant of the API.

This strongly suggests `backend_optimization_plan_for_budget_with_facts` /
`backend_optimization_decisions_for_budget_with_facts` in
`src/compiler/60.mir_opt/general_patterns.spl` either does not implement
fact-gating for these specific optimizer rules (ssa-var-canon,
simple-loop-unroll, simple-predicate-promote, simple-strength-reduce,
simple-scalar-cleanup, simple-auto-vectorize, simple-hot-call-inline,
llvm-entry-alloca-shaping), or implements it but does not emit a
`skipped_decisions` entry with the expected `reason` string when a required
fact is absent — a genuine gap between the REQ-OPJH-022/025/026 spec's stated
contract and the current implementation. Not root-caused further (out of
scope for this triage pass; no src/** edit attempted).

## Repro (trimmed)

```
use compiler.mir_opt.general_patterns.{backend_optimization_plan_for_budget_with_facts}
val missing = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir"])
# missing.recommendation_names correctly excludes "ssa-var-canon"
var found = false
for decision in missing.skipped_decisions:
    if decision.stable_name == "ssa-var-canon" and decision.reason == "missing ssa.var_transform":
        found = true
print(found)   # false, expected true — no skipped_decisions entry carries this reason
```

Not touched further: `test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl`
had one unrelated `.?` truthiness fix applied (line 34: `reason.?` → `reason != nil`,
matching the documented `.?`-on-a-value landmine and confirmed by re-run: failures
dropped from 9 to 8). The remaining 8 failures are genuine and were left untouched —
weakening these assertions would violate the no-weakening rule.
