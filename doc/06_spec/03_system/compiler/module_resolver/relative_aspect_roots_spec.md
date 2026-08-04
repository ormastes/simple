# Resolver-Owned Relative Aspect Roots

> Executable source: `test/03_system/compiler/module_resolver/relative_aspect_roots_spec.spl`

| Tests | Active | Skipped | Pending |
|---:|---:|---:|---:|
| 9 | 9 | 0 | 0 |

## Purpose and audience

This scenario manual is for resolver, build, and security reviewers. It
describes executable evidence for REQ-AF-004 and the root-validation portion of
REQ-AF-007.

## Preconditions

- Use a current pure-Simple full CLI with `SIMPLE_LIB=src`.
- Run from the repository workspace so the declared fixture manifest resolves.
- Do not use the Rust seed or create host-dependent symlink fixtures.

## Operator workflow

1. Supply explicit root candidates and the declaring manifest path.
2. Resolve manifest-relative canonical paths and concrete variant roots.
3. Inspect deterministic rank/identity ordering and the selection fingerprint.
4. Reject an invalid aspect root registry before any root set is published.

## Scenarios

### REQ-AF-004: manifest-relative deterministic build-time resolution

- **should canonicalize roots from the declaring manifest and order by rank and identity** — checks normalized physical paths and deterministic ordering.
- **should bind concrete variant roots and the selection fingerprint at build time** — checks selected platform/hardware roots and fingerprint propagation.
- **should keep logical aspect identity stable across physical root locations** — checks a move changes physical path without changing `aspect_id`.
- **should install resolved roots on the live resolver without exposing them to core importers** — checks the resolver-owned root snapshot, registry fingerprint, and hidden-import boundary.

### REQ-AF-004 and REQ-AF-007: fail-closed root validation

- **should reject manifest-relative traversal outside the workspace** — requires
  `E-APATH001` and zero roots.
- **should reject a physical symlink escape from a lexically contained path** —
  requires `E-APATH002` from the lexical/physical containment oracle.
- **should permit an explicitly declared external physical root** — checks the
  explicit `external: true` policy exception.
- **should reject same-rank duplicate aspect identities without publishing roots** —
  requires `E-APATH003` and zero roots.
- **should discard valid candidates when any root in the registry is invalid** —
  proves registry-wide atomic failure rather than partial acceptance.

## Pass/fail criteria

PASS requires all nine examples to execute, every concrete path, ordering,
fingerprint, and diagnostic assertion to pass, and zero skipped or pending
examples. A crash, partial root publication, missing scenario, or seed execution
is FAIL.

## Evidence and provenance

- Requirements: `doc/02_requirements/feature/aspect_facet_dynload_smf_pack.md`
- Test plan: `doc/03_plan/sys_test/aspect_facet_dynload_smf_pack.md`
- Design: `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
- Executable source SHA-256:
  `fc678e3842736a34050f8b38e8947ba0ddc9452735d68a4ead9b4d7ebdf951e8`

<details>
<summary>Executable SSpec</summary>

The complete executable source is the sibling evidence artifact at
`test/03_system/compiler/module_resolver/relative_aspect_roots_spec.spl`.
It is authoritative for helper bodies and assertions.

</details>

## Compatibility and limitations

The symlink-oriented case invokes the resolver's lexical-versus-physical
containment oracle directly and does not mutate the host filesystem. This spec
proves build-time root materialization; it does not claim runtime catalog or
loader traversal because runtime receives only concrete catalog identities.
