# Selected C2 increment: pure nominal bodies

Parent: selected robust plan C2 / REQ-MC-007, lane 07 semantic data export. This increment implements an already selected capability; it does not select a new language or broaden C4/C5.

| Requirement | Contract |
|---|---|
| NB-01 | Struct Aggregate uses the admitted nominal symbol, exact field order/count/types, and exact destination type. Empty and nested structs are supported. |
| NB-02 | Enum Aggregate selects the explicit retained discriminant, requires zero operands for nullary variants or exactly one operand of the retained payload type, and preserves nominal destination identity. |
| NB-03 | GetField on an admitted struct resolves the declaration index and emits its qualified projection with an exact destination type. |
| NB-04 | Const/Copy/Move glue and return preserve exact types; local IDs are unique/nonnegative, arguments agree with the known nonvariadic signature, uses must be defined/live, and reassignment is rejected. |
| NB-05 | Nominal bodies require one exact acyclic entry-to-Ret path of Goto edges (NB-08), or one terminal Bool branch with two disjoint returning paths (NB-09). Unsupported mixed operations, enum projection, mutation and arbitrary control flow fail closed. Existing non-nominal bodies retain the prior translator. |
| NB-06 | Both backend owners' full/generated module APIs use the same admitted context and fail without returning partial source. |

Out of scope: arbitrary arithmetic/calls in nominal bodies, aggregate updates, enum elimination, general CFG, heap aliasing, native layout refinement, proof closure and Minimal mode axiom policy. Whole C2 remains partial.

## Selected C2 continuation: mixed scalar statements (NB-07)

Within the admitted nominal single-block body, accept the existing scalar operator policy with additional exact type checks: Add/Sub/Mul/BitAnd/BitOr/BitXor on I8/U8/I16/U16/I32/U32/I64/U64; Eq/Ne on those integers, Bool, Char and Unit, with Bool result; Neg/BitNot on fixed-width integers; Not on Bool. Operand MIR types must be identical, destination type must match the operator result, and all ordinary liveness/single-assignment checks apply.

Operator text and unsupported-policy errors come from the existing lean_mir_translate owner. Division/remainder, ordered comparison, powers and shifts remain refused. Checked arithmetic, casts, calls, CFG, mutation and aggregate equality remain outside this increment. Earlier out-of-scope arithmetic wording is superseded only for this exact admitted set. Scalar-only functions continue through the original translator. This adds no native representation/refinement claim and does not complete C2.

## Selected C2 continuation: linear aggregate flow (NB-08)

Follow `entry_block` and actual `Goto` targets rather than physical block order. All block IDs must be unique/nonnegative; the selected entry and every visited successor must exist. The path must consume every block exactly once and end in `Ret`. Reject cycles, disconnected blocks and all other terminators before publishing source. Preserve one exact-type, definition and move-liveness environment across edges. Support arbitrary block IDs, reordered storage and empty intermediate blocks without rendering labels or copying statements into multiple paths.

This extends NB-05 and NB-07 only from one block to one linear path. Branching, joins/phi, loops, exceptional control flow, calls, mutation, recursive nominal types and unions remain required future C2 work. It grants no trust/replay or native ABI authority. Both full/generated APIs of both backend owners must exercise the real typed-MIR path. All new scenarios are authored UNRUN until a qualified runner is available.

## Selected C2 continuation: terminal branch flow (NB-09)

One actual MIR `If` may terminate a linear entry prefix. Each retained successor must be a disjoint, nonempty linear Goto chain ending in an exact-typed Ret. All input blocks must belong to exactly one prefix/arm; duplicate/negative IDs, missing edges, cycles, shared successors/merges, nested If, Switch and exceptional terminators fail before publishing source. Physical block order is irrelevant.

The condition must be a defined/live exact Bool operand. Its Move is consumed before state splitting. Each arm starts with fresh assigned/live maps containing the prefix's scalar state and validates its own instructions/return. A local defined only in one arm cannot become available in the other; the same incoming value may be moved in both mutually exclusive arms. Validate both arms even for a literal Bool condition. Bodies with no retained nominal type or nominal operation retain their existing translator, including scalar-only Result routes.

This supersedes the NB-08 blanket conditional refusal only for that exact shape. General branching, joins/phi, loops, calls/mutation, union and recursive fixed-vector semantics, C1/C6/C7 qualification remain open. Actual full/generated APIs of both retained backend owners must exercise these obligations. Authoring or source review does not qualify Lean/native execution or memory/performance.

NB09-01 admission correction: nominal Struct/Enum evidence in the retained return type, parameters or locals selects the typed nominal translator even with no Aggregate/GetField. Supported Array/Slice/Tuple/Result wrappers are inspected for such evidence; a Result containing only scalar types does not itself select the nominal route. This detector grants no owner/type authority: existing context/signature/local validation must still reject unresolved or kind-mismatched nominal rows. Instruction-free Struct/Enum conditional returns and Copy/Move are required direct/full/generated API controls with literal qualified signatures.

## Selected C2 continuation: one diamond join (NB-10)

A single Bool branch may rejoin one shared linear return suffix. The entry prefix and the two exclusive arm prefixes must be disjoint, and the first shared block must begin identical returning suffixes; empty arm prefixes are permitted. Validate unique/nonnegative identities, target existence, all retained block coverage, no cycles/prefix backedges, and no nested or unsupported terminators before emitting source. Keep the existing separate-return NB-09 shape.

Each arm receives fresh assignment/liveness maps after condition consumption. The join retains assignment history by union and read availability by intersection. A local defined or moved on only one arm cannot be read in the suffix; any earlier assignment on either arm prevents suffix redefinition. Independently defined same-identity locals can join only with the common exact MIR type. Dominating live values remain outer bindings. Transport newly defined both-live values in retained local-vector order through an explicitly typed Unit/single-value/product conditional binding, and emit/validate the shared suffix once. Both arms must be checked even for literal conditions; only the selected arm is evaluated by emitted Lean.

NB-10 extends NB-09 only for this one-diamond shape. It does not admit general nested CFG, loops, Phi, mutation/drop/calls, unions or recursive fixed vectors, and grants no C1/C6/C7 trust/refinement authority. All new and reconciled actual API scenarios remain UNRUN until qualified execution.

## CV-01: exact pure composite values (C2/C5)

Admit fixed Array and Tuple constants, Array/Tuple aggregates and Tuple GetField using retained exact element/component types. Array size must be nonnegative and equal actual arity; tuple arity and destination type must match. Array uses the existing Vector representation with a typed literal and definitional length witness; tuple zero/single/multiple representations remain Unit/identity/right-associated products. Nested Struct/Enum elements use actual admitted local values; unsupported nominal constant encodings are not guessed.

Preserve ordered single evaluation and existing Copy/Move liveness, including terminal branches and shared-suffix joins. Recursively expand constants only within128 levels (root1) and65536 visited nodes per function, charging before expansion. The then branch consumes the common remaining scalar budget; the fresh else state receives its remainder, and the suffix receives else's remainder. State maps remain independent. Preserve fixed-width integer Zero; unsupported leaf kinds refuse.

All prior nominal route selections remain. Composite types alone select the typed owner only without Calls; existing call-only composite wrappers retain their exact previous flat export. Actual composite operations and constant operands force typed validation even with Calls, preventing fallback around checks. No typed Call authority is added. Public full/generated module errors publish no successful source; no caller-owned builder transaction guarantee is invented.

Pointer/heap indexing, mutable composites, checked arithmetic, recursive Vector, union semantics, general CFG and full C1–C7 trust/refinement obligations remain OPEN. This fragment is semantic MIR-to-Lean source export, not native box/unbox/layout equivalence. Physically boxed MIR operands with inconsistent retained element types refuse. All authored scenarios are UNRUN until qualified execution.
