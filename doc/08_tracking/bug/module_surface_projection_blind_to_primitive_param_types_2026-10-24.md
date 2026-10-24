# Surface semantic projection does not distinguish primitive parameter types

Status: open. Found 2026-10-24 while adding the TLDR surface skeleton
(module_surface_skeleton_v1 / module_surface_canonical_digest_v1).

## Repro (Rust seed, `run`)
```
val a = parse_full_frontend("pub fn add(a: i64) -> i64:\n    a\n", "fx.spl", "fx", Logger(level: 0))
val b = parse_full_frontend("pub fn add(a: i32) -> i64:\n    a\n", "fx.spl", "fx", Logger(level: 0))
module_surface_semantic_projection(a) == module_surface_semantic_projection(b)   # true (cb86867b...)
```
Renaming the function does change it (ffcb077a...).

## Why it matters
`module_surface_semantic_projection` (src/compiler/20.hir/hir_lowering/module_surface_semantic_projection.spl)
is the declaration identity behind `module_surface_declaration_matches` and the
frozen-surface limbs. `_surface_param` folds `_surface_type_digest(value.type_)`
= `ast_semantic_encode_type` (generated ast_semantic_value); if that encoding
collapses primitive types, a parameter-type-only edit of a dependency does not
change its surface identity, so dependents' cached HIR can be reused stale.

## Next
Check `ast_semantic_encode_type` for primitive kinds on the self-hosted binary;
if it reproduces there, encode the primitive kind/name. Until fixed, the
skeleton/full-parse equality (which uses this projection) cannot detect a
type-only divergence.
