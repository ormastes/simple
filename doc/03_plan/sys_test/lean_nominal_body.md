# Nominal body system tests

41 authored body scenarios after the current-base port, all UNRUN. Owner `lean_nominal_body_spec.spl` exercises exact whole emitted bodies and full/generated plugin APIs: ordinary/nested/empty structs, sparse and negative enum tags, projection, constant/copy/move/unit return; counterexamples cover arity, signedness, nominal type, payload, index, undefined/missing/duplicate/redefined/moved locals, return type, control flow, mutation and signature authority. `compiler_lean_nominal_body_spec.spl` exercises both compiler-owner module APIs with exact constructor output and sparse-tag success/ordinal refusal.

NB-01: struct/order, arity/type/destination, nested/empty cases. NB-02: sparse/negative tags and payload negatives. NB-03: projection/index/type/enum negatives. NB-04: local/return/signature/constant/copy/move cases. NB-05: CFG/mutation refusal. NB-06: both owner public APIs.

These are production API calls with actual MirModule values and complete output/error oracles. They are not an executed acceptance result, generated Lean elaboration, native refinement proof or measured coverage percentage. Execution requires a qualified runner; none is launched in this source task.

Revision 2 adds one nested multiline builder oracle per backend owner, for 26 total scenarios. Cycle 1 identified only the physical-line indentation blocker C2-BODY-01.

## Mixed scalar continuation

10 new authored scenarios, 36 cumulative, all Simple execution UNRUN. Plugin owner loops over all eight integer MIR kinds and all six arithmetic/bitwise operations; Eq/Ne cover 11 scalar kinds; Neg/BitNot cover eight integer kinds and Not covers Bool. Each successful case checks the complete contiguous typed operation/construction/projection/return body through both full/generated APIs. Negative cases check signedness, result type, unsupported representation/operator, consumed operands and redefinition. A scalar-only exact function oracle verifies prior delegation. Compiler owner adds mixed arithmetic/equality and signedness refusal through its real two APIs.

NB-07 traces to these scenarios and lean_nominal_body's BinOp/UnaryOp arms. Prior nominal-only cases remain byte-preserved except helper imports/insertion. A bounded hand-authored Lean target check may establish only reference syntax/definitional computation; it cannot mark these Simple API scenarios passed or prove the generator.

## Current-base semantic Char boundary (2026-10-20)

Four additional scenarios cover both retained backend owners. Typed Char arguments
construct and project a nominal field through full/generated exports using Lean
Char. Integer constants tagged Char are refused for negative, surrogate and
out-of-range payloads and also otherwise valid ASCII/astral integers: there is
no admitted integer-to-Char constant adapter. This is an explicit intermediate
unsupported feature, not validation by normalizing a malformed scalar.
The full selected Unicode-scalar requirement remains open for constants and
source/native correspondence. Physical inline UTF-8 storage is outside C2.

Current-base argument-count oracle: missing, duplicate and out-of-range Arg
indices refuse through the real nominal-body owner and both module exports.
Existing successful zero/one/multiargument exports protect against always-refuse
behavior. The completeness counter increments only after row validation, with no
Dict.len dependency, keys allocation or extra traversal. This additional scenario
brings the body total to 41; all remain UNRUN.

NB-08 adds 32 authored UNRUN scenarios in `lean_nominal_linear_flow_spec.spl` and `compiler_lean_nominal_linear_flow_spec.spl` (16 each), using the real full/generated APIs and exact direct emitted body. The three prior CFG refusal assertions now name cycle, missing-entry and disconnected-block errors. Existing 41 body scenarios remain; none was executed or relabeled PASS. See the two matching linear-flow manuals for the new scenario mapping. The full nominal body inventory is now 73 authored scenarios, not 73 executed successes.

NB-09 adds 40 authored UNRUN terminal-branch scenarios across the two new owner-specific specs (20 each). The previously prepared 73 body scenarios remain; their linear-flow conditional refusal is narrowed to the actual shared-successor graph, and its diagnostic wording names the current supported terminators. No test execution is claimed; the inventory becomes 113 authored body scenarios. Both-arm moves, condition/prefix consumption, sibling-local isolation, either-arm return errors and graph refusals use actual public export APIs.

Cycle2 NB09-01 adds eight actual API scenarios: instruction-free Struct/Enum selection, nominal Copy/Move, unresolved/kind-mismatched nominal refusal and scalar/Result identity controls, mirrored across both backend owners. All remain UNRUN; baseline failure is source-predicted only.
