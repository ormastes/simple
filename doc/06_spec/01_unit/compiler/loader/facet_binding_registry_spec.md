# Facet Binding Registry

> Executable source: `test/01_unit/compiler/loader/facet_binding_registry_spec.spl`

## Purpose

Proves atomic facet publication, exact/open-world lookup, generation isolation,
and ordered resolved method lookup. A published record stores a loader-owned
`FacetWitnessDescriptorV1`; its descriptor symbol is inert identity, while its
method entries contain the executable ordinary-SMF addresses.

## Operator-visible flow

1. Stage a binding only after descriptor owner, ABI hash, and method addresses
   have been resolved.
2. Publish the candidate for one exact activation key and generation.
3. Resolve the concrete or open-world facet record.
4. Select a method by canonical name or contract order.
5. Reject absent names, out-of-range method indexes, ambiguity, and stale
   generations with typed diagnostics.

PASS requires the named and ordered lookups to return the same resolved method
address without invoking or exporting an executable factory.
