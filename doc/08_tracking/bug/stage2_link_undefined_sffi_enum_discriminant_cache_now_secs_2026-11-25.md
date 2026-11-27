# Stage 2 link failure: undefined `_sffi_enum_discriminant` / `_cache_now_secs` (2026-11-25)

Status: FIXED (this commit)
Lane: `--full-bootstrap --stop-after-stage2` on release/1.0.0 @ a7183f66456
(aarch64-unknown-linux-gnu, llvm)

## Symptom

Stage 2 native-build compiled all 1,619 modules, then failed at link:

```
mold: error: undefined symbol: _sffi_enum_discriminant
>>> referenced by compiler__mir___MirLoweringExpr__method_calls_literals
mold: error: undefined symbol: _cache_now_secs
>>> referenced by compiler__frontend__cache_dir_evict
```

The build's own note: "reached the linker undeclared because HIR lowering
resolved it to nothing and the `lenient_types` fallback lowered it to a
global."

## Root cause

Two independent unresolved identifiers, both introduced by recent commits:

1. `method_calls_literals.spl` (06350eaa7dd, Dict.get_or MIR lowering)
   called `_sffi_enum_discriminant<MirTypeKind>(...)`. That helper is
   module-private in the sibling modules `expr_dispatch.spl` and
   `enum_constructor_payload.spl`; a `use ...*` import does not export
   underscore-private names, so the identifier resolved to nothing in
   `method_calls_literals.spl`. The module already owns an identical private
   helper, `_sffi_method_hir_type_discriminant` (same
   `compiler_value_discriminant<T>` body, same `@always_inline`).

2. `cache_dir_evict.spl` (fdaf3463e64, worker/memory budget scaling) called
   `_cache_now_secs()` in `cache_dir_reap_stale_tmp_v1`, a function that is
   defined nowhere in the tree.

## Fix

1. `method_calls_literals.spl`: call the module's existing
   `_sffi_method_hir_type_discriminant<MirTypeKind>` at the three sites
   (identical semantics — tagged type-kind discriminant via the canonical
   `compiler.common.value_access` owner).

2. `cache_dir_evict.spl`: compute `now` from the already-declared
   `rt_time_now_unix_micros()` extern (`now_micros / 1000000`), the exact
   idiom `cache_dir_evict_to_cap` in the same file already uses.

## Verification

Seed single-file `check` is not authoritative for these modules (the seed
rejects pre-existing constructs: `HirExprKind::NullCoalesce`, `While`,
`For`). The authoritative gate is the Stage 2 rebuild: both modules
previously compiled to objects and only the link failed on exactly these two
symbols; both replacement idioms already compile elsewhere in the same
files.
