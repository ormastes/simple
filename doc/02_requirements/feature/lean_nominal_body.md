# Selected C2 increment: pure nominal bodies

Parent: selected robust plan C2 / REQ-MC-007, lane 07 semantic data export. This increment implements an already selected capability; it does not select a new language or broaden C4/C5.

| Requirement | Contract |
|---|---|
| NB-01 | Struct Aggregate uses the admitted nominal symbol, exact field order/count/types, and exact destination type. Empty and nested structs are supported. |
| NB-02 | Enum Aggregate selects the explicit retained discriminant, requires zero operands for nullary variants or exactly one operand of the retained payload type, and preserves nominal destination identity. |
| NB-03 | GetField on an admitted struct resolves the declaration index and emits its qualified projection with an exact destination type. |
| NB-04 | Const/Copy/Move glue and return preserve exact types; local IDs are unique/nonnegative, arguments agree with the known nonvariadic signature, uses must be defined/live, and reassignment is rejected. |
| NB-05 | Nominal bodies require one exact entry block and Ret. Unsupported mixed operations, enum projection, mutation and arbitrary control flow fail closed. Existing non-nominal bodies retain the prior translator. |
| NB-06 | Both backend owners' full/generated module APIs use the same admitted context and fail without returning partial source. |

Out of scope: arbitrary arithmetic/calls in nominal bodies, aggregate updates, enum elimination, general CFG, heap aliasing, native layout refinement, proof closure and Minimal mode axiom policy. Whole C2 remains partial.

## Selected C2 continuation: mixed scalar statements (NB-07)

Within the admitted nominal single-block body, accept the existing scalar operator policy with additional exact type checks: Add/Sub/Mul/BitAnd/BitOr/BitXor on I8/U8/I16/U16/I32/U32/I64/U64; Eq/Ne on those integers, Bool, Char and Unit, with Bool result; Neg/BitNot on fixed-width integers; Not on Bool. Operand MIR types must be identical, destination type must match the operator result, and all ordinary liveness/single-assignment checks apply.

Operator text and unsupported-policy errors come from the existing lean_mir_translate owner. Division/remainder, ordered comparison, powers and shifts remain refused. Checked arithmetic, casts, calls, CFG, mutation and aggregate equality remain outside this increment. Earlier out-of-scope arithmetic wording is superseded only for this exact admitted set. Scalar-only functions continue through the original translator. This adds no native representation/refinement claim and does not complete C2.
