# Generic TLDR acquisition table (XXH3 bucket + full-key verify) is absent on release/1.0.0

- Status: open (gap, not a regression)
- Found by: packet E3 (`generic-tldr-identity-controls`), 2026-11-01
- Owner file: `src/compiler/00.common/cache_contract/generic_tldr_view_v1.spl`

## Observation

The header of `generic_tldr_view_v1.spl` states that XXH3 "is used only as an
in-memory bucket index by the acquisition table, and every bucket hit is
verified against the full canonical key". On `release/1.0.0` no such
acquisition table exists (`grep -rn concrete_tldr_key_v1 src` matches only the
contract file), so there is no injectable bucket-hash seam and no production
full-key verify function.

## Impact

The collision-safety property is a stated contract, not a verified property.
`test/01_unit/compiler/cache/generic_tldr_view_v1_spec.spl` (REQ-GENERIC-TLDR-E3-002/003)
covers it only with a spec-local constant-hash bucket over the real
`concrete_tldr_key_v1` keys.

## Expected fix (separate packet)

When the acquisition table lands, expose its bucket hash as an injectable
parameter and retarget the E3 controls at the real lookup.
