# Target 6 typed HIR receipt (2026-09-29)

`cold_hir_typed_receipt_from_admitted_entry_v1` now returns a compact
`ColdHirTypedReceiptV1`: the inventory-bound semantic seed and canonical ABI
payload bytes. It validates the HIR source path and frozen source content,
encodes the typed HIR interface once, and hashes those same bytes into the
seed's ABI digest. Existing seed callers project this receipt without a
second encoding pass.

The unit SPipe source checks payload equality, digest equality, and changed
source rejection. The existing native probe also checks the new receipt. The
pure Simple Stage2 compiler built that probe with `--entry-closure`,
`--backend cranelift`, and `SIMPLE_NO_STUB_FALLBACK=1`: 292 compiled, zero
failed, 269 KB executable. Executing it returned
`PASS cold_hir_batch_native_probe`.

This is a producer API, not a production graph publication. The driver does
not yet retain the receipt before HIR/source eviction or pair it with real
compiled archive receipts. There is also a scope mismatch to solve: the V2
index builder rejects fewer drafts than `.spl` entries in the admitted source
inventory, but entry-closure compilation need not lower every inventory
module. The cold producer must define and verify its complete graph scope
before the CLI can publish a V2 generation. No full compile performance or
memory claim follows from this focused probe.
