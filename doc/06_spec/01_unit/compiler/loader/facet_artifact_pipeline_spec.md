# Facet Artifact Pipeline

> Executable source: `test/01_unit/compiler/loader/facet_artifact_pipeline_spec.spl`

## Purpose

Proves the versioned facet artifact and executable call boundary used by SHB,
ordinary SMF, the loader, and native performance fixtures. The canonical
`witness_symbol` is inert descriptor identity and a method-symbol prefix, never
an executable factory export.

## Frozen steps

1. Derive the canonical witness symbol and reject declared-only or unrelated
   emission.
2. Admit all contract-ordered method symbols and reject empty/generic
   descriptor shapes.
3. Project facet metadata and behaviorally parse the retained ordinary
   function.
4. Round-trip current contract metadata and decode the prior v1 layout.
5. Round-trip binding metadata and reject runtime owner/address authority at
   the wire encoder.
6. Open/map the deterministic ordinary-SMF fixture, resolve every ordered
   method to one exact owner/address, and reject ABI/owner mismatch.
7. Build and resolve deterministic ASCII/UTF-8 multi-symbol exports; reject
   invalid names, ranges, tables, and non-relocatable input.
8. Resolve the published witness operand and lower its indirect call.
9. Lower a resolved method with the base as ABI argument zero and reject a
   signature without a receiver parameter.

PASS requires deterministic codec round trips, discovery of the named
`.facet_bindings` ordinary-SMF section and its exported witness method, and a
`CallIndirect` retaining the explicit resolved address. Generic facet-method
syntax is outside this artifact/runtime boundary. Artifact emission must fail
when any contract-ordered witness-method symbol exists only as declaration
metadata. Encoding must also reject a runtime-populated descriptor rather than
silently discarding its owner or resolved addresses. Receiver-aware method invocation prepends the
base operand and then uses the same `CallIndirect` instruction; an incompatible
signature fails with `E-AF005`.
Multi-symbol SMF coverage verifies `.text`-relative offsets, per-symbol code
slices, symbol counts, and UTF-8 byte-based string-table offsets through the
real in-memory loader.

## Probe fixture

`test/fixtures/aspect_facet/runtime_fixture.spl` exports
`facet_runtime_fixture_binding()` and `facet_runtime_fixture_smf()`. Runtime
probes resolve `FacetBindingRecord.witness_descriptor.method_entries`, use
`AspectApplicationRuntime.acquire_published_facet_method(...)` for the exact
ordinary-SMF method address plus lease, and release that lease through
`release_facet_generation_lease(...)`.
