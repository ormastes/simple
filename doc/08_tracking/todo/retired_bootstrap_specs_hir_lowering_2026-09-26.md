# Retired bootstrap specs: HIR / frontend lowering contracts

- **Filed:** 2026-09-26
- **Status:** open — re-land the feature, then restore the spec from its origin commit
- **Component:** `src/compiler/20.hir/hir_lowering/`, `src/compiler/10.frontend/core/types.spl`

## Why these were retired

Brought in by the share-history squash `e274cd33719` (2026-08-27). It has a
single parent, and its unsquashed twin `a8244005f9b` on
`origin/chore/merge-share-history` is single-parent too, so no source-branch
commit survives. The branch implementation is not in the `e274cd33719` tree
either: `fcbec1c3b62` restored `src/compiler` to origin. The specs failed on
Windows bootstrap46 under the delegated seed. Owner decision 2026-09-26: retire
and track.

## Missing features

| Spec (test/01_unit/compiler/bootstrap/) | Retired | Missing on main | Origin commit |
|---|---|---|---|
| `bootstrap_flat_if_tail_lowering_spec.spl` | 16 examples (2 kept) | `lower_bootstrap_flat_stmt` / `_expr` handle only expression, return and declaration tags. Missing: flat if/elif/else lowered to `HirExprKind.IfChain` (value-producing, no fabricated else for the `EXPR_UNIT` sentinel), while/for/continue (labeled and unlabeled), for-iterable resolved before iterator shadowing, typed locals with loop-scope shadowing, expression-block tails scoped to their preceding `Let`, typed raw `Expr` payload decoding, and fail-closed handling for unsupported tags, out-of-range if-chain owners, exhausted recursive budget, indirect expression-block cycles, tuple iterator names and negative operands | `e274cd33719` / `a8244005f9b`; last pre-squash main version of the spec: `0e7b9f985e1` |
| `hir_import_resolution_shared_binding_contract_spec.spl` | whole file | No immutable `HirResolvedImportModule` result; `module_import_resolution.spl` still reassigns `var resolved_module_name` | `e274cd33719` / `a8244005f9b` |
| `hir_module_lowering_shared_binding_contract_spec.spl` | whole file | Mutable optional accumulators remain (`var found` / `found_name` / `arith_name` in `module_callable_types.spl`, `var flat_ret_val` / `value` in bootstrap module declarations) | `e274cd33719` / `a8244005f9b` |
| `newunit_pool_reset_contract_spec.spl` | whole file | `reset_all_pools()` in `core/types.spl` never resets `newunit_names` / `newunit_suffixes` / `newunit_underlying_type_tags`; there is no newunit project authority (reset at compile-route entry, promote before transient teardown, commit after surface success). **Possible latent bug, not just a missing feature:** newunit pools may leak across compilations in one process | `a8244005f9b` (pre-squash copy of the same merge; no earlier branch commit carries this blob) |

## Re-land checklist

1. Land the feature on main.
2. `git show e274cd33719:test/01_unit/compiler/bootstrap/<spec>` and restore
   the spec (or its retired examples). Escape literal `{` in needles as `\{`.
3. Run it under the seed and the self-hosted CLI; it must pass on both.
