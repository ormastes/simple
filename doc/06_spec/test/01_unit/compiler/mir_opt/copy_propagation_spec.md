# CopyPropagation Skeleton Specification

Copy propagation is currently classified as `Skeleton` and must not transform
MIR through canonical or direct compatibility entrypoints.

| Contract | Expected evidence |
|---|---|
| Honest statistics | A new pass reports zero propagated uses and eliminated copies. |
| No direct bypass | The source contains none of the former chain-walk, block, instruction, operand, or terminator rewrite helpers. |
| Ownership safety | No dormant `Move` rewrite exists while consuming-move semantics are unproved. |

Future activation requires a basic-block-local `Copy`-only positive witness,
exhaustive MIR operand/terminator coverage, dominance and redefinition kills,
cycle-safe near-linear chain resolution, exact candidate/change/rejection
receipts, post-pass verification, and semantic differential tests. `Move` may
only participate after ownership and destruction timing are proved.

Source: `test/01_unit/compiler/mir_opt/copy_propagation_spec.spl`.
