# Nominal body export — authored manual

Status: authored from the accompanying executable SSpec source, not runner-generated; all scenarios UNRUN.

Step: Construct and project admitted nominal values. Inputs include ordered U8/I32 Packet fields, nested/empty structs, and State variants with tags -3 and 12. Check exact emitted constructor/projection bodies and both module APIs.

Step: Reject mismatched aggregate evidence. Change field count/type, nominal destination, payload, tag or projection index. Both APIs must return the expected error, never successful partial source.

Step: Preserve unsupported-state boundaries. Exercise missing/redefined/moved locals, wrong return/signature, multiple blocks and mutation. Require failure. Supported constant/copy/move glue remains exact.

Step: Exercise the retained compiler backend owner. The separate compiler-owner spec checks complete constructor text and sparse discriminant behavior through its full and generated APIs.

This manual records intended checks only. No test pass, Lean acceptance, proof closure or whole-C2 completion is claimed.

## Mixed scalar continuation — authored, UNRUN

Step: Preserve typed scalar computation across aggregate construction and projection. For every admitted width and operator, call the real plugin module APIs and compare the exact typed scalar/constructor/projection/return block. Check Eq/Ne Bool results and valid unary operators.

Step: Check mixed-body wiring in the retained compiler owner. Exercise signed multiplication, inequality and a signedness mismatch through both compiler APIs.

Refusals include wrong operand/destination types, unsupported scalar/type pairs, division/order/powers/shifts, use after move and reassignment. Scalar-only output must remain unchanged. Ten added scenarios bring the authored total to 36; none were executed in Simple.

## Current-base Char semantic boundary — authored, UNRUN

Step: Export a typed Unicode-scalar argument into a nominal field, then project
it through both full/generated module APIs in both backend owners. Assert the
actual `_root_.Char` parameter/result signature and qualified projection.

Step: Attempt integer-valued MIR constants tagged Char for -1, both surrogate
range endpoints, U+110000, ASCII A and U+1F600. Both module APIs must return the
existing exact fixed-width-integer refusal; no guessed conversion or generated
proof is accepted. Valid scalar integers are included to document that the
constant adapter itself is unsupported, rather than claiming scalar validation
has been implemented. Four additional scenarios bring body coverage to 40
**authored, UNRUN** scenarios. C7 physical representation and C6 replay authority
remain independent outstanding gates.

Current-base argument-count oracle: missing, duplicate and out-of-range Arg
indices refuse through the real nominal-body owner and both module exports.
Existing successful zero/one/multiargument exports protect against always-refuse
behavior. The completeness counter increments only after row validation, with no
Dict.len dependency, keys allocation or extra traversal. This additional scenario
brings the body total to 41; all remain UNRUN.
