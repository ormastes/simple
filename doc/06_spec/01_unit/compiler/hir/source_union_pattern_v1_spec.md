# Source union narrowing binder

Source: `test/01_unit/compiler/hir/source_union_pattern_v1_spec.spl`.
Requirement: `REQ-C2-UNION-BINDER-001`.
Status: **UNRUN**. This manual records intended assertions, not execution evidence.

The public frontend parses source and HIR lowering enters the match arm scope.
A valid union type pattern must define its typed payload before the guard and
body resolve names. Canonical union identity and the existing synthesized enum
registry determine the variant; the emitted payload contains exactly one binding.

| Scenario | Required observation |
| --- | --- |
| Guard and body with outer-name shadow | Both references use the payload SymbolId, which differs from the outer parameter; payload and symbol declaration are i64. |
| Text narrowing | The body references the Text payload binding with the Str type. |
| Absent union member | Exact E-NARROW-002 names the requested arm and canonical union; the requested binder remains unresolved. |
| Nonunion subject | Existing E-NARROW-001 remains visible and no binder is invented. |
| Arm scope isolation | A binder from the preceding arm remains unresolved in the next arm. |
| Nested matches | Different subjects use different registry owners and guard/body binders; following outer arms retain the outer owner. |
| Named union member | Payload and symbol type identify the actual Packet declaration; both guard operands and body use the same binder. |
| Wrong named member | A visible Other declaration is rejected with E-NARROW-002 and its requested binder remains unresolved. |

Every accepted primitive or nominal arm checks the emitted Named owner against
both actual structural-union registry directions. Its one-element payload type
must be a normalized member and select exactly that member's canonical variant.

Canonical preparation has an explicit source-level once-per-match boundary:
`expression_core` prepares before the arm loop; preparation returns at the first
TypeTest/Or occurrence, and all arm/Or lowerings receive that local value.
The binder helper performs no normalization. Nested matches receive fresh local
contexts. Nonunion matches return before scanning patterns or allocating a
description. The existing later union/nil narrowing route remains unchanged.
This is a source work-bound argument, not measured runtime or speedup evidence.

The scenarios fail on missing MatchCase, wrong payload form or arity, detached
symbols, untyped payloads, missing diagnostics, or leaked bindings. They do not
claim native execution, formal translation, or complete union value transport.
