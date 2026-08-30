# Self-host HIR cache encoding segfaults in `hc_enc_hir_type` (2026-08-22)

Status: OPEN (P1 compiler correctness blocker)

## Reproduction

Using the freshly admitted Stage 2 compiler from commit `b22c425c43e`, run a
one-file native build with the default frontend cache enabled. The source only
declares and calls `rt_mem_snapshot_open`; its contents are not required to
trigger the crash. The compiler reaches HIR post-diagnostics and exits 139.

## Measured backtrace

```text
hc_enc_hir_type
hc_enc_hir_symbol
hc_enc_symbol_table
hc_enc_hir_module
hir_module_encode
hir_cache_store
CompilerDriver.lower_and_check_impl
CompilerDriver.compile
```

The same admitted compiler reaches the snapshot-open fail-closed diagnostic
when `SIMPLE_MEM_SNAPSHOT_FILE` is set, before cache storage. Stage 3 recovery
sets `SIMPLE_FRONTEND_CACHE=0`, so this cache crash is distinct from the
snapshot ABI defect fixed by `b67c3e5a881` and from the open Stage 3 RSS issue.

## Next evidence

Reproduce after the snapshot ABI fix has been rebuilt into Stage 2, inspect the
`HirType` value entering `hc_enc_hir_type`, and compare generated
`hc_enc_symbol_table` / `hc_dec_symbol_table` fields with `SymbolTable` before
changing cache format or promotion ownership.
