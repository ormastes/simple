<!-- codex-research -->
# Feature options: checked aspect-component admission

## Option A — Canonical component-resolver bridge

Add an explicit `aspect_pack_smf` component kind and catalog path/digest fields.
Resolve one canonical component identity, keep static selection I/O-free, and
route dynamic startup selection through one persistent `ModuleLoader` that
registers the pack and atomically installs its catalog.

- Pros: connects existing checked pieces; one owner; enables later
  packaging and typed facets; supports real lifecycle/invalidation evidence.
- Cons: requires reconciling component and dynSMF identity/stale-static rules.
- Effort: M, approximately 3–5 Pure Simple source/spec/manual files.

## Option B — DynSMF-owned persistent bridge

Add the explicit aspect component metadata directly to the checked dynSMF
manifest and route it into one persistent `ModuleLoader`, while retaining the
current common component resolver as an independent static-planning API.

- Pros: smaller identity migration and a direct checked startup-to-loader path.
- Cons: leaves two resolution APIs whose consistency needs permanent contract
  coverage; future packaging must target the dynSMF metadata shape.
- Effort: M, approximately 3–4 files.

## Option C — Full packaging and typed facets in one slice

Add component admission, native-build pack/catalog production, real compiler
grammar/type/HIR/MIR lowering, `FacetRef<T>`, and executable witness dispatch.

- Pros: delivers the largest visible language feature at once.
- Cons: XL blast radius; crosses several currently disconnected models; makes
  failures and performance regressions difficult to localize.
- Effort: XL, more than 20 files across compiler, loader, runtime, and docs.
