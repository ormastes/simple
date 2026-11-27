# Optional accepted for a concrete constructor field

Status: OPEN; distinct from the accessor source repair.

The retained daemon producer accepted `HirExpr(type_: returned, ...)` with
`returned: HirType?` although `HirExpr.type_` is HirType. Native aggregate copying
then interpreted a Some enum header as a Span pointer. See
[retained evidence](accessor_optional_concrete_storage_2026-10-30.md).

Required follow-up: locate the constructor argument compatibility check and reject
an optional-to-concrete assignment unless the language specifies an explicit checked
conversion. Add a negative typed-constructor regression and positive concrete and
explicit-unwrapping controls. Confirm the failure occurs before native copying.
The retained evidence proves this acceptance gap, not its exact validator owner or
a general backend defect. No validator change or executable reproduction is claimed.
