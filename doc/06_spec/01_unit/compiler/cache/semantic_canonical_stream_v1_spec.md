# Semantic canonical stream V1 compatibility

Source: `test/01_unit/compiler/cache/semantic_canonical_stream_v1_spec.spl`.
Trace: REQ-CSM-003/006. Manual intent; native execution/docgen **UNRUN**.

Existing executable scenarios retain the frozen Begin01 scalar vector,
integer widths/ranges, float bits, UTF-8 framing, canonical map/set ordering,
record ordering, variants/options, limits, container/root errors, duplicates,
finish rules and revision projection expectations. Mutating calls now use
explicit mutable receivers. The separate owner spec checks persistent state
without relying on finishing a copied helper parameter.

Run with `<runtime> test <spec> --native`; generate with
`<runtime> spipe-docgen <spec> --output doc/06_spec --no-index` after admission.
Require zero stubs. This manual supplies no runtime PASS.
