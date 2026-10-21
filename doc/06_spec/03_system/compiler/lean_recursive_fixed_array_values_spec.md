# Recursive fixed-array constructor source specification

Source: `test/03_system/compiler/lean_recursive_fixed_array_values_spec.spl`.
Requirement: C2 / REQ-C2-RV-002. Eleven authored scenarios; **zero executions**.
This is a manually maintained source specification, not generated test output.
Compiler, SPipe, generated-Lean/kernel, native, allocation and performance checks
are **UNRUN**. Source-predicted RED before the change is not a measured failure.

The fixtures construct real typed MIR, obtain the actual declaration planner's
context and invoke the shared nominal emitter. Positive output helpers also call
full and generated exports through both retained backend owners, and compare the
borrowed module's canonical serialization before and after. Expected-text helpers
only spell the expected terms: they never call production mapping or carrier
selection to derive an expected answer.

| Scenario | Real oracle |
|---|---|
| Ordered operands and binder hygiene | Exact body puts `_l1, _l0` in one typed Vector initializer before the Fin lambda; source local names deliberately equal the new binder names. |
| Empty aggregate and constant | Both routes capture an empty, explicitly typed Vector and require no `Tree` inhabitant. |
| Nested constants | Two independently scoped empty inner captures are initialized before the outer index lambda. |
| Nested aggregate locals | Inner carrier is constructed once; outer initializer contains its two local references in Copy/Move order without rewrapping or indexing them. |
| Unselected nominal length | Exact prior Vector body is retained when only a different array length is selected. |
| Selected aggregate budget | Three units admit one root plus two operands; two units refuse before consuming either Move or assigning the destination. |
| Constant budget | Existing root/leaf count admits three nested Array nodes exactly; a two-node allowance refuses. Selection adds no second constant charge. |
| Empty and ordinary aggregate budgets | Selected empty aggregate needs one unit; zero refuses. An unselected aggregate retains its existing zero additional charge. |
| Ordinary scalar constant | Exact U8 Vector literal for 1 and 255 is unchanged alongside a recursive selected shape. |
| Repeated Move | Actual operand liveness rejects the second consumption before returning a body; input serialization is unchanged. |
| Count and nominal-kind errors | Actual emitter refuses one operand for length two and a Struct element referring to an Enum declaration. |

Step labels reuse the approved constructor contract: “Construct and transport
finite arrays”, “Preserve source and declaration authority”, and “Refuse malformed
or over-budget export”.

The implementation shares the existing cumulative `constant_nodes_left` allowance
for selected aggregate construction: one root plus every retained operand term is
charged before the terms array grows. Literal operands also pay their existing
constant traversal charge. This is a logical work/term bound, not a total memory,
provider capacity-scan, whole-module output-size or runtime allocation bound.

The classifier and completed context belong to the declaration planner. No
test-injected carrier map or alternative naming policy is used. Source parsing,
retained/materialized defaults and validated enum continuations are covered by
separate lanes and are not claimed by these constructor-only cases. Output
spelling checks do not establish Lean positivity, evaluation or finite-sequence
correspondence; generated-module Lean acceptance remains required separately.
