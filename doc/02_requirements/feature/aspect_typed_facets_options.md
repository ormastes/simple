<!-- codex-research -->
# Typed facet feature options

## F1 — Static typed acquisition first (recommended)

Add a dedicated `FacetAcquire` expression (not a generic method-call rewrite),
with selected spelling, explicit `try|lazy|required` mode, selected source of
language-level contract/type identity, selected witness/dispatch representation,
and selected diagnostic/error behavior.  Lower it over the existing
non-executable pack loader.  Existing string facet keys and pack ABI hashes
remain admission data, not typed language contract identity.  Keep executable
mapping release unavailable.

Pros: smallest compatible language step; prevents fake dynamic-unload claims;
uses current indexed catalog.  Cons: does not complete open-world executable
facets.  Effort: L, about 20–30 files.

## F2 — Lifecycle bridge before language surface

First add a loader-owned V2 receipt/lease registry with exact owner, mapping,
and generation identity; grammar follows later.

Pros: resolves the critical executable-unload foundation first.  Cons: no user
visible typed syntax initially; requires mapper API hardening.  Effort: M/L,
about 15–25 files.

## F3 — Full open-world typed facets

Deliver grammar, type/witness ABI, resolver admission, executable dispatch, and
V2 lifecycle together.

Pros: reaches the complete target in one program.  Cons: highest integration,
compatibility, and lifecycle risk.  Effort: XL, 50+ files.
