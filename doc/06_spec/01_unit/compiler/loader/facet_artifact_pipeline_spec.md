# Facet Artifact Pipeline

> Executable source: `test/01_unit/compiler/loader/facet_artifact_pipeline_spec.spl`

## Purpose

Proves the versioned facet artifact and executable call boundary used by SHB,
ordinary SMF, the loader, and native performance fixtures.

## Frozen steps

1. **Emit facet contract metadata**
2. **Consume facet contract metadata**
3. **Emit facet binding metadata**
4. **Consume facet binding metadata**
5. **Open the deterministic facet SMF fixture**
6. **Resolve the fixture witness symbol**
7. **Resolve the published witness operand**
8. **Lower the witness call**
9. **Derive the canonical witness symbol**
10. **Reject a declared-only facet implementation**
11. **Admit an actually emitted witness symbol**
12. **Project declared facet implementation metadata**
13. **Inspect the retained executable source**

PASS requires deterministic codec round trips, discovery of the named
`.facet_bindings` ordinary-SMF section and its exported witness, and a
`CallIndirect` retaining the explicit resolved address. Generic facet-method
syntax is outside this artifact/runtime boundary. Artifact emission must fail
when the canonical witness exists only as declaration metadata; the projection
scenario separately proves that facet method signatures remain available as
metadata while ordinary executable source is retained.

## Probe fixture

`test/fixtures/aspect_facet/runtime_fixture.spl` exports
`facet_runtime_fixture_binding()` and `facet_runtime_fixture_smf()`. Runtime
probes use `FacetBindingRecord.resolved_witness_address`,
`AspectApplicationRuntime.acquire_published_facet(...)`, and
`release_facet_generation_lease(...)`.
