# Application Aspect Catalog Activation

> Executable source: `test/03_system/app/simple/aspect_catalog_activation_spec.spl`

| Tests | Active | Skipped | Pending |
|---:|---:|---:|---:|
| 7 | 7 | 0 | 0 |

## Purpose and audience

This manual is for loader, dynSMF, AOP, and release reviewers. It covers
REQ-AF-003 and REQ-AF-006..008 plus deterministic, cold-path, bounded-resource,
and compatibility NFRs.

## Preconditions

- Use a current pure-Simple full CLI with `SIMPLE_LIB=src`.
- The SFM2 codec, exact-digest provider, catalog, dynSMF, and generation owners
  must be available.
- Do not use the Rust seed or codegen stub fallback.

## Operator workflow

1. **Inspect the application Aspect Catalog.**
2. **Acquire the optional facet.**
3. **Load only the selected SMF module closure.**
4. **Publish the facet generation atomically.**
5. **Reject an invalid aspect pack.**

## Scenarios

- **keeps manual and lazy facets cold after catalog inspection** — resolves a
  concrete route while pack-open, selected-byte, mapping, sidecar, and scan
  counters remain exactly zero.
- **loads only the dependency closure and publishes one generation** — stages
  two selected 128-byte SMFs, advances the existing lifecycle once, and does
  not claim executable mapping.
- **coalesces concurrent requests for the same catalog key** — one owner
  publishes while in-flight and active followers reuse its generation.
- **rejects an invalid selected module without changing the prior generation**
  — requires an actual SHA-256 mismatch and exact coordinator preservation.
- **rejects invalid catalog topology policy and compatibility before
  publication** — covers cycles, undeclared policy, and target mismatch.
- **preserves dynSMF disable controls and rejects stale requests atomically** —
  preserves prior session, lifecycle, binding table, reservations, and counters.
- **publishes open-world lookup then unbinds only the exact generation** —
  resolves a concrete implementing type through its business interface and
  proves exact-generation unbind removes the visible witness.

## Pass/fail criteria

PASS requires all seven scenarios, real assertions, zero placeholders, exact
digest validation, and no generation/counter change on a failed transaction.
A crash, seed execution, partial publication, or claimed executable mapping is
FAIL.

## Evidence and provenance

- Requirements: `doc/02_requirements/feature/aspect_facet_dynload_smf_pack.md`
- Test plan: `doc/03_plan/sys_test/aspect_facet_dynload_smf_pack.md`
- Design: `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
- Executable source SHA-256:
  `4816927d9c8148d423ea92eefb6dab48b35095d5015401c17354294e7d7feeea`

<details>
<summary>Executable SSpec</summary>

The sibling executable source is authoritative for fixture/helper bodies and
assertions, including `build_aspect_pack_fixture`,
`verify_cold_aspect_counters`, and `verify_atomic_activation`.

</details>

## Compatibility and limitations

The counters are scoped to the catalog/activation adapter, which receives an
already-open validated provider. This slice proves control-plane staging,
binding publication/lookup, and exact unbind contracts; it does not claim
executable relocation/mapping, generation-pin drain, cache eviction, or
dynamic advice patchpoint execution.
