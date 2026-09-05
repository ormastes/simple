# Stage 2 omits split impl providers from the native entry closure

Date: 2026-08-22
Status: PARTIAL — Phase 2 admitted; focused specs and Stage 3 pending
Owner: compiler module closure / split impl registration
Severity: P0 for current ARM64 bootstrap and SimpleOS QEMU rendering

## Exact failure

After restoring `PatternKind.TypeTest`, a strict ARM64 trust-root Phase 2
compiled the full closure and failed at link with six undefined method symbols:

- `HirLowering.union_narrow_arms`, defined only in
  `_Expressions/union_narrow_arms.spl`;
- `MethodResolver.fill_call_defaults`, `resolve_call_args`,
  `resolve_call_result_type_raw`, `resolve_comp_clause`, and
  `resolve_verification_contract`, defined only in
  `35.semantics/resolve_lookup_helpers.spl`.

Both provider files extend a type declared by their caller module, but no live
module imported the provider. Native entry-closure discovery therefore had no
edge that could retain either object. The fix explicitly imports each split
impl provider from its owning caller module, matching the existing compiler
driver split-impl registration pattern.

## Evidence required

1. Fresh strict Phase 2 links and passes its sanity and struct-receiver gates.
2. The union-narrowing and generated-visitor specs remain green.
3. Stage 3 no longer reports these six undefined symbols.

No seed fallback, weak symbol, fabricated stub, or whole-tree inclusion is an
acceptable substitute for the explicit owner-to-provider closure edges.

## Current evidence

The third guarded cycle produced and admitted Phase 2 SHA-256
`2090f5506fc5ba218d3526f3ae49f121b16e97a04b70a4c9ec1674a5773a315b`;
the six undefined method symbols are absent from the canonical link, and both
admission gates pass. A standalone full-compiler regression build is still
blocked by 16 separately owned unresolved runtime symbols, so criteria 2 and 3
remain open and this record is not resolved.
