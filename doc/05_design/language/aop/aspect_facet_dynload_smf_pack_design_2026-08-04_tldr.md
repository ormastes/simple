# Aspect Facet / Dynload Pack Design — TLDR

The design extends the existing SFM, loader, dynSMF, AOP, cache, and compiler
owners. The outer artifact is an SFM aspect pack containing opaque ordinary-SMF
modules; facets never mutate the base object's nominal layout.

## Core Shape

- Source facet acquisition lowers to a private typed `(Base, FacetContract)`
  adapter with an opaque, affine generation lease.
- `AspectExecutionContext` is the only application gate owner for activation,
  lazy reservation/I/O/commit, facet leases, advice dispatch, and unload.
- Exact-route lazy activation reserves before external I/O, revalidates the
  catalog/provider/activation key at commit, and uses the canonical loader and
  cache. `try_facet` remains no-I/O.
- Prepared advice uses typed v2 context injection and stable compiler ABI
  leaves: prepare under the gate, native callback outside it, then finalize and
  release exact-generation pins under the gate.
- Gate/split transitions, lazy activation, facet lifecycle, ordinary unload,
  compiler ABI wrappers, and the embedding pack-I/O port are implemented.

## Verification Status

- Implementation status is static-only: source guards pass and
  `aspect_application_runtime.spl` is below 800 lines.
- `STATUS: FAIL` remains authoritative. Executable evidence is absent for
  concurrency/interleavings, callback-error cleanup, stale lazy commits,
  admitted self-host/backend execution, generated manuals, coverage, and NFRs.
- Production image/signature port deployment, imported/indirect unwind support,
  leaf-level lease visibility, and startup configuration remain blockers.

## Open Next

- [Full design](aspect_facet_dynload_smf_pack_design_2026-08-04.md)
- [Agent plan](../../../../03_plan/agent_tasks/aspect_facet_dynload_smf_pack.md)
- [Verification report](../../../../09_report/verify_aspect_facet_dynload_smf_pack.md)
- [Runtime owner](../../../../../src/app/startup/aspect_application_runtime.spl)
