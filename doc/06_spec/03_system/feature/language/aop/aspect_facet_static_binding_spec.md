# Static Aspect-Facet Binding

> Executable source: `test/03_system/feature/language/aop/aspect_facet_static_binding_spec.spl`

| Tests | Active | Skipped | Pending |
|---:|---:|---:|---:|
| 16 | 16 | 0 | 0 |

## Purpose and audience

This scenario manual is for compiler, AOP, and release reviewers. It describes
the executable evidence for REQ-AF-001, REQ-AF-002, REQ-AF-003, REQ-AF-009,
and REQ-AF-010 in the implemented static attached-witness slice.

## Preconditions

- Use a current pure-Simple full CLI with `SIMPLE_LIB=src`.
- Do not use the Rust seed or codegen stub fallback.
- The P1 type-predicate, P4 facet semantics, and static `std.aop.facet` modules
  must be present.

## Operator workflow

1. Parse and lower the feature-scoped facet declarations.
2. Check coherence against the base descriptor projection.
3. **Acquire the optional facet.**
4. Repeat structural selection with the descriptor registration order reversed.
5. Exercise the required, ambiguity, access, and core-dependency failures.

## Scenarios

### REQ-AF-001: core independence and layout stability

- **should build only an attached witness plan** — accepts one plan and proves
  its representation is `Attached`.
- **should reject nominal introduction from the static attached slice** —
  requires `E-AF005` and no published plan.
- **should reject a core dependency on an optional aspect declaration** —
  requires `E-AF001`.

### REQ-AF-002: typed explicit acquisition

- **should acquire a typed already-linked facet witness** — checks the typed
  view and binding identity.
- **should return no facet when the typed identity is absent** — checks `nil`.
- **should retain the exact dynamic generation lease and lazy sidecar handle** —
  checks that a dynamic `FacetRef<T>` carries application-issued generation
  identity and external state without changing the base layout.
- **should activate only when optional acquisition policy permits it** — checks
  the typed activated view.
- **should return typed required-facet absence without implicit activation** —
  checks `RequiredFacetAbsent`.
- **should reject a required binding whose implementation is incomplete** —
  requires `E-AF002` and no plan.

### REQ-AF-003: deterministic structural selection

- **should select the same implementation when base descriptors register first**.
- **should select the same implementation when the aspect plan is evaluated before base order**.
- **should reject ambiguous single-provider bindings** — requires `E-AF003`.
- **should fail closed for an ambiguous short selector name** — requires
  `E-AF004` and no plan.

Both successful registration-order scenarios require `CacheDebug` and evaluate
the shared `TypePredicateBytecode` against `storage.cache.LruCache`.

### REQ-AF-009: public capability boundary

- **should publish public-readonly access in every accepted plan**.
- **should reject a facet implementation without the V1 public-readonly capability**.

### REQ-AF-010: existing AOP preservation

- **should leave existing advice and CE bind syntax outside facet parsing**.
- **should accept a module containing only established AOP and CE forms without inventing facets**.

## Pass/fail criteria

PASS requires all 16 examples to execute, every concrete value/diagnostic
assertion to pass, and zero skipped or pending examples. `CompileResult.Success`
alone is not acceptance. Any missing example, matcher failure, crash, or seed
execution is FAIL.

## Evidence and provenance

- Requirements: `doc/02_requirements/feature/aspect_facet_dynload_smf_pack.md`
- Test plan: `doc/03_plan/sys_test/aspect_facet_dynload_smf_pack.md`
- Design: `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
- Executable source SHA-256:
  `1d6cbc31e46a9ee420b2f0243c7825766028a7e416a7e92d91f098eea1870d14`

<details>
<summary>Executable SSpec</summary>

The complete executable source is the sibling evidence artifact at
`test/03_system/feature/language/aop/aspect_facet_static_binding_spec.spl`.
It is authoritative for helper bodies and assertions.

</details>

## Compatibility and limitations

This evidence covers no-I/O `try_facet`, policy-controlled optional acquisition,
and typed required acquisition. It does not claim arbitrary private-layout
access or independently implement loader publication and dynamic unload.
