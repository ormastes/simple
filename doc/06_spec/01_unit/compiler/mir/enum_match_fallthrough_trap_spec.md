# Enum match fallthrough

Authored companion for `test/01_unit/compiler/mir/enum_match_fallthrough_trap_spec.spl`.
Execution and generated documentation: UNRUN for this follow-up.

The existing scenarios inspect real lowered MIR for partial, statement,
guarded, total, and intentional-default matches. They require panic plus Abort
for unmatched values and preserve the explicit-default opt-out.

The REQ-002 addition lowers a Copy/Move/Const return-operand enum twice, before
and after adding Borrow. Both fixtures use the same explicit classifier.
Require no HIR errors, a real classifier function, exactly one fallthrough
Abort, and a panic call in its block. Only the extended enum must name Borrow
in the missing-variant diagnostic and trap. This uses frontend/HIR/MIR behavior,
not a source-string check or synthetic coverage object.

Root must run this under robust using the admitted producer. The asserted
behavior is diagnostic plus divergent MIR; robust compile rejection, actual
native trap execution, critical wildcard wiring, and formal proof are not
established by this spec.
