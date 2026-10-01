# Stage-2 CLI: `hir_cache_store` encodes a garbage `HirSymbol.type_` handle (0xC0000005)

**Status:** open. **Host:** Windows x86_64-pc-windows-msvc, stage-2 self-hosted `simple_cli.exe`
(admitted #1604 tree) and a rebuild of it carrying #16xx's flat-pool owner fix.

## Symptom

`simple_cli run <file importing compiler.backend.backend_types>` (278-module closure) with a
published frontend cache scope (`SIMPLE_FRONTEND_CACHE_SCOPE=<x>`) dies with 0xC0000005 after
~30 s / 5.5 GB. This is the crash previously described as "HIR of compiler.backend.backend_types
with a warm frontend parse cache" (`D:/wk-wc` investigation, PR #1610 notes).

## What it is NOT

- Not the frontend parse cache's pool-owner replacement (fixed separately): the rebuilt CLI with
  that fix crashes identically (`b2_new_cold`: rc=0xC0000005, 32 s, 5.5 GB; `b2_new_warm`: same).
- Not cache-hit dependent: cold (0 hits, 278 stores) and warm both crash.

## Discriminator (measured 2026-09-26, primed `D:/wk-fable-base` checkout)

| run | frontend scope | `SIMPLE_HIR_CACHE` | result |
|---|---|---|---|
| old CLI | armed | default | 0xC0000005, 29 s, 5.5 GB |
| old CLI | `SIMPLE_FRONTEND_CACHE=0` | default | exit 1 (ordinary HIR diagnostics), 100 s |
| fixed CLI | armed | default | 0xC0000005, 32 s |
| fixed CLI | armed | `0` | exit 1 (ordinary HIR diagnostics), 85 s |

The crash needs the on-disk **HIR cache store**, which runs only when a cache scope is published.

## cdb + PDB evidence (`cli_fixed_dbg.exe`, `/DEBUG` relink of the stage-2 CLI)

```
(2bac.1084): Access violation - code c0000005
cli_fixed_dbg!compiler__hir__generated__hir_codec__hc_enc_hir_type+0x8c:
    mov r8, qword ptr [rcx]   ; rcx = f198715900000000
  hc_enc_hir_type
  hc_enc_hir_symbol+0x41d
  hc_enc_symbol_table+0xbe
  hc_enc_hir_module+0x447
  compiler__hir__hir_codec__hir_module_encode+0x18d
  compiler__driver__driver_hir_cache__hir_cache_store+0x1c8
  CompilerDriver.lower_and_check_impl+0x28e6
```

`hc_enc_hir_type(w, node)` reads `node.kind`; `node` (a `HirSymbol.type_`) is
`0xf198715900000000`, i.e. the 8 bytes at offset +4 of an `RtCoreEnum`
(`transient_scope_id=0`, `enum_id=0xf1987159`) -- a HirType slot that no longer holds a HirType.
No `rejected invalid array handle` line precedes it, so this is not the or-pattern payload
defect fixed in the seed by this PR's sibling commit; it is a stale/mis-typed handle inside the
symbol table that only the codec (which walks every symbol's type) ever dereferences.

## Next step

Break on `hc_enc_hir_symbol` with the symbol name printed (`%ma` on the name handle), find the
first symbol whose `type_` is not a registered raw allocation, and trace where that symbol's
`type_` was last written (type inference after `promote_symbol_table_transient_owners`, or a
symbol table row that `lower_retained_surface_module`'s promotions do not cover).
Repro: `cp D:/wk-wc/.wc/probe/probe_bt.spl .; SIMPLE_FRONTEND_CACHE_SCOPE=x SIMPLE_FRONTEND_CACHE_DIR=<empty> simple_cli run probe_bt.spl`.
