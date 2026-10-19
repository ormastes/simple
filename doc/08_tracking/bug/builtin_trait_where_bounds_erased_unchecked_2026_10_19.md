# builtin_trait_where_bounds_erased_unchecked_2026_10_19

- Status: open
- Severity: correctness gap (silent accept), no crash
- Found: 2026-10-19, review of PR #3887

## Defect

Builtin trait where-bounds are erased in HIR; they are not checked by
type_infer obligations. `HirLowering.bound_is_undeclared_builtin_trait`
(`src/compiler/20.hir/hir_lowering/types.spl`) drops bare `Clone`, `Copy`,
`Debug`, `Default`, `Drop`, `Eq`, `Ord` bounds that have no declared symbol, so
`collect_function_bounds_from_module`
(`src/compiler/30.types/type_infer/traits.spl:56-70`) never records them and
the obligation check (`traits.spl:178-181` ->
`src/compiler/25.traits/trait_validation.spl:34` "trait bound not satisfied")
never runs for them. `fn f<K>(k: K) where K: Ord` called with a non-Ord type is
silently accepted. This is the pre-`5b649fb61fe` status quo, kept to unblock
Phase 3 (`eq_ord_where_bound_unresolved_hir_2026_10_19`).

## Why not resolve them now

Lowering the bounds to `builtin_trait_symbol(id, name)` (ids 1-7 in
`create_builtin_traits`) would need builtin impls of those traits for the
primitive and text types. The solver has none, so every call would be falsely
rejected.

## Fix direction

Register builtin impls (Eq/Ord for ints, floats, bool, char, text, etc.) in
the trait solver, then lower builtin bounds to their builtin trait symbols
instead of erasing them, and add a negative spec (`where K: Ord` with a
non-Ord struct must fail).

DB reconciliation pending (`simple check-dbs` not run on this host).
