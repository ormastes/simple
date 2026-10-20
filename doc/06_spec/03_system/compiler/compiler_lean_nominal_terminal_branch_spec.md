# Typed nominal terminal branches — compiler.backend.backend.lean_backend

Source: `test/03_system/compiler/compiler_lean_nominal_terminal_branch_spec.spl`. Requirement NB-09 / C2 / C4 / REQ-MC-007. Status: 20 authored scenarios, all **UNRUN**. This is a manually maintained source manual, not generated execution evidence.

The fixture constructs actual MIR modules, declarations, signatures, operands and edges. Every case exercises both full/generated public APIs; positive cases additionally assert exact shared-body text. Refusal requires the actual error cause; successful output fails the negative scenario. There is no mock translator, proof certificate or alternate runner.

| Case | Observable obligation |
|---|---|
| 1 | Actual Bool branch and two exact returns |
| 2 | Reordered physical storage |
| 3 | Goto prefix and disjoint continuation |
| 4 | Both arms move the same incoming value |
| 5 | Condition Move consumed before split |
| 6 | Nominal return from both arms |
| 7 | Unchanged linear-flow control |
| 8 | Wrong or missing condition |
| 9 | Consumed condition unavailable in either arm |
| 10 | Prefix-consumed value unavailable in either arm |
| 11 | Then-only local cannot leak to else |
| 12 | Both return types checked under literal true |
| 13 | Inherited assignment cannot be redefined |
| 14 | Missing/shared successor refusal |
| 15 | Cycle/nested/disconnected refusal |
| 16 | Duplicate ID/unsupported terminator refusal |
| 17 | Instruction-free Struct/Enum selection with exact owner-qualified signature |
| 18 | Independent Copy/Move without Aggregate/GetField and exact nominal terms |
| 19 | Unresolved or kind-mismatched nominal evidence refuses direct and both module APIs |
| 20 | Scalar-only and scalar-only Result identity routes preserve output |

The move and definition controls distinguish fresh per-arm mutable storage from aliased map handles. Both branches are validated despite runtime mutual exclusion. Shared return blocks, nested branches and merges remain unsupported; no branch is silently ignored. See the detail design for the complete outstanding C1–C7 ledger and source-only memory/performance boundaries.

The cycle2 routing controls were authored before the production selection fix. The detector follows retained supported type shapes and does not authenticate or repair nominal identities. Expected signatures/terms use literal qualified names; they are not computed from the mapper being tested. All execution remains UNRUN.
