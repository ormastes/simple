# Feature Requirements: Environment-Optimized Dynamic Libraries

**Selection:** Feature Option A — catalog-selected sibling artifacts; target-ID
Option B — target-triple-derived versioned registry; inspector Input Option 1 —
atomic immutable stdin at start
**Dates selected:** 2026-09-07 (provider architecture), 2026-09-08 (target-ID
and inspector-input authority)

- **REQ-001:** The system shall keep one baseline-safe core and select optimized sibling provider artifacts without requiring a whole-executable ISA matrix.
- **REQ-002:** `EnvironmentSnapshotV1` shall separate host execution architecture/ABI, hardware features, OS-usable features, policy-allowed features, execution domain, vector-state contract, loader permissions, and bounded GPU device facts from generated-code target intent.
- **REQ-003:** `VariantDescriptorV1` shall bind provider/variant identity, contract version and ABI digest, semantic/grammar/program identity, placement, exact CPU/OS/device requirements, artifact digest/location, dependency closure, memory/effect/numerical contracts, and bounded resource requirements.
- **REQ-004:** Eligibility shall reject incompatible or untrusted variants before preference ranking and, for native candidates, before executable mapping whenever inert metadata is available.
- **REQ-005:** Selection shall implement distinct `prefer`, `require`, and `max` semantics; no override may manufacture capability, cross architectures, bypass trust, or silently satisfy an unsupported required request.
- **REQ-006:** `BindingPlanV1` shall publish deterministic, immutable, generation-pinned dense facet bindings with dependency locks, policy/environment identities, selected variants, and bounded rejection reasons.
- **REQ-007:** Native, SMF, static, and later JIT placements shall expose the same logical typed provider contract while reporting metadata admission, mapping, callability, execution, completion, and retirement as distinct states.
- **REQ-008:** `FrontendFacetV1` shall provide coarse session/batch parsing operations without exposing compiler-private AST/HIR layouts, and shall preserve the independent legacy CPU frontend as the reference path.
- **REQ-009:** The initial optimization pilot shall vary parser providers only; canonical scalar parity shall precede SIMD promotion, and incomplete dialect coverage shall never become the default.
- **REQ-010:** Generated-code target features shall be independent of the host parser implementation; requested, backend-accepted, artifact-declared, emitted, selected, and executed SIMD facts shall be reported separately.
- **REQ-011:** GPU providers shall remain placement siblings rather than SIMD tiers and shall reuse the existing GPU registry/service through adapters with enabled-feature, program, resource, fence, and retirement evidence.
- **REQ-012:** Provider replacement shall use new-session cutover and retain old generations until CPU calls, sessions, callbacks, JIT references, GPU work, buffers, and completion objects drain.
- **REQ-013:** CPU-only help/version/reference compilation shall not initialize optional GPU machinery, and production startup shall not compile a missing optimized provider.
- **REQ-014:** Every selection, rejection, fallback, binding, execution, completion, quarantine, and rollback shall have a stable explainable receipt bound to exact environment and artifact generations.
- **REQ-015:** Target ABI, object-format, OS, and architecture numeric identities shall be assigned by a repository-owned, versioned canonical target-triple registry. Aliases shall normalize to one canonical tuple; unknown or ambiguous triples shall fail closed; registry version and mapping digest shall participate in target-profile, cache, plan, and receipt identity.
- **REQ-016:** Production binary inspection shall start an identity-owned process with one bounded immutable byte input. The process owner shall bind input digest/count to tool, argv, environment, process generation, bounded output captures, terminal status, exact stdin completion/closure, and reap before issuing an inspection authority token.

## Initial scope

The next implementation slice adds the canonical target-triple registry owner
and atomic-byte owned-process V3 inspector authority, then joins their opaque
live tokens to the existing target profile and binary-inspection projections.
SIMD parser artifacts, generated dynlib/JIT/AOT specialization, and GPU-resident
execution remain staged extensions that must reuse these contracts.

## Exclusions

No new source grammar, independent plugin framework, whole-executable environment matrix, hidden startup compilation, per-token dynamic lookup, or claim of SIMD/GPU execution without emitted/executed evidence.
