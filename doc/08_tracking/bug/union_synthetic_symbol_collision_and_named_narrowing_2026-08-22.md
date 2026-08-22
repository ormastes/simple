# Structural union symbol and named-narrowing follow-up

## Status

Partially resolved by the module-owned SymbolTable registry and bare named-type
lookup. Generic/qualified pattern grammar remains open. Static audit only; no
compiler execution was permitted.

## Remaining correctness risks

`union_synth_symbol_id` remains the preferred-ID function for compatibility,
but production synthesis and HIR narrowing now reserve through the same
module-owned `SymbolTable` registry. Name-to-ID and reverse ID-to-name maps
recompute the preferred ID from canonical identity and probe on collision;
enum and variant IDs use the same owner and survive HIR codec round trips.

The registry prevents aliasing, but a genuine same-hash pair still receives
its two probed IDs in encounter order. Encounter-independent artifacts require
sorted preregistration before lowering embeds either ID. The exported legacy
synthesis wrappers also remain compatibility-only and do not coordinate IDs
across independent calls.

Bare named source patterns now resolve their registered SymbolId before key
lookup. The pattern grammar still carries only one identifier plus binder, so
generic arguments and qualified/composite type syntax cannot reach HIR and
remain unsupported.

## Completion conditions

- Generic and qualified type-test grammar carries a real frontend Type and HIR
  pattern carries/resolves a HirType rather than spelling only.
- Generic type-test arms resolve through complete structural HIR identity.
- Collision and named/generic fixtures prove exact enum, variant, payload, and
  diagnostic behavior.
- Sorted preregistration makes genuine same-hash assignment independent of
  declaration and dictionary traversal order.
