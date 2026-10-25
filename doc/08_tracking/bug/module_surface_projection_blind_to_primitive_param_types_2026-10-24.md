# Surface semantic projection does not distinguish primitive parameter types

Status: Fixed (2026-10-25). Found 2026-10-24 while adding the TLDR surface skeleton
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

## Fix
Root cause was not primitive-type collapse in `ast_semantic_encode_type`: the
generated encoder updated a COPY of its SHA-256 stream (`val stream =
state.stream; stream.update(...)`), so on the seed every type/expr/stmt digest
was the empty-input hash. Fixed in `d289f5ee758` (stream written back);
regression `test/01_unit/compiler/hir/module_surface_primitive_type_identity_spec.spl`.
Skeleton/full equality incl. this fixture and a differential over five
`src/lib/common` files: `test/01_unit/compiler/driver/worker_surface_differential_spec.spl`.
With the blind spot gone, the HIR worker skeleton path is default ON
(`SIMPLE_HIR_WORKER_SKELETON=0` opts out); see
`worker_whole_closure_parse_2026-10-25.md`. Spec run on this Windows host is
blocked by the known seed parse error in `windows_redirected_process.spl`.
