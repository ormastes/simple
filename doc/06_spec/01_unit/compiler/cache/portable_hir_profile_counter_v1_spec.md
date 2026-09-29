# Portable HIR profile body-object counter V1

Executable source:
`test/01_unit/compiler/cache/portable_hir_profile_counter_v1_spec.spl`.

## Contract

The typed semantic owner is the single authority for a decoded HIR object's
`body_objects` reservation. The profile facade may reserve encoded and
retained bytes after bounded decode, but must not reserve the object a second
time. Consequently, a `max_body_objects: 1` ledger admits one valid object,
reports `body_objects == 1`, and refuses a second charge with the typed
`BoundsExceeded("body object budget")` result while leaving the counter at 1.

The executable contract checks both the bounded ledger transition and the
delegation boundary: the profile facade calls typed semantic validation without
a local body-object charge, and the semantic owner has exactly one such charge.
This preserves counter agreement between direct typed validation and the future
decoded profile path.

## Authority status

This correction does not change admission. Base + Portable schema 2 remains
the only declared representation; byte-verifier availability, completeness,
encoder admission, and native-loader admission remain false/closed pending
their separate authority owners.
