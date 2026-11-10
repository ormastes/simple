# native_method_result_overwrites_receiver_slot_2026_10_21

Status: open. Workaround pinned by n88b_native_workaround_shapes_spec; native repro n88b_native_producer_idioms_native.spl; real fix still needed (20.hir/50.mir type propagation or runtime class layout). Native-codegen defect (HIR/MIR); source @workaround sites: src/compiler/10.frontend/generated/ast_semantic_value.spl.
The real fix is in 20.hir/50.mir type propagation (owned by phase-3 agent a508755bae341480a); not changed here.

## Workaround pinned only (n88_b, 2026-11-04) - real fix still open

Source repair/workaround is pinned by `bin/simple.exe test test/01_unit/compiler/80.driver/n88b_native_workaround_shapes_spec.spl` (8/8 pass on the seed).
Native repro fixture: `test/fixtures/compiler/n88b_native_producer_idioms_native.spl` (+ `.expected`); covers the WRITEBACK_ line (bool-returning method then field writeback).

Stage3 repro (expected: no diff output, exit 0; then remove the matching `@workaround` tags):

```
bin/simple native-build --entry test/fixtures/compiler/n88b_native_producer_idioms_native.spl -o build/n88b_idioms.exe && build/n88b_idioms.exe | diff - test/fixtures/compiler/n88b_native_producer_idioms_native.spl.expected
```

## Root cause + fix (2026-11-09)
Native repro on `stage2_new4.exe` (fixture WRITEBACK line, `h.counter.bump(5)`
where `bump` does `self.total = self.total + n`): `WRITEBACK_0_1` (expected `5_1`).
MIR dump of `Counter.bump`: `GetField l3 = self.0; l4 = l3 + n; Copy l3 <- l4` and
NO `SetField` -- the update never reaches the object, regardless of the bool result.
Cause: `collection_desugar` Pattern B rewrites `x.f = x.f + <ident>` into
`x.f.merge(<ident>)`; `lower_unresolved_array_merge`'s scalar/text arms compute a NEW
value and call `emit_method_writeback`, but `merge` was missing from
`is_mutating_method`, so the write-back kind stayed 0 and no store was emitted.
Fix: add `merge` to `is_mutating_method` (switch_operators_calls.spl). Spec
`test/01_unit/compiler/50.mir/merge_field_update_writeback_spec.spl` 2/2 green,
0/2 with the fix reverted. Native re-verification needs a rebuilt producer.

## 2026-11-10 P2 triage (lane p2-compiler-triage-20261110)

VERDICT: SUPERSEDED on source. Root fix present: switch_operators_calls.spl:9674
`case "merge": true` in is_mutating_method (9653), commit 6c86fde0319a, ancestor
of release/1.0.0 d7a430cc2baf. Qualified on the deployed seed (interpreter):
merge_field_update_writeback_spec.spl 2/2; workaround pin
n88b_native_workaround_shapes_spec.spl 8/8. @workaround tag at
ast_semantic_value.spl:30 intentionally retained until the stage3 repro runs
(native-build of test/fixtures/compiler/n88b_native_producer_idioms_native.spl,
exact command in build/review/p2fix-compiler-20261110.sdn). Cycles: 1.
