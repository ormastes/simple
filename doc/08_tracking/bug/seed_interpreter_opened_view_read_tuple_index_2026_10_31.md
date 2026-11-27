# Phase 1 seed: `case Ok(value): value` mis-binds when a spec imports `std.common.json.value` (FIXED)

Symptom (2026-10-31, Phase 1 seed, `SIMPLE_EXECUTION_MODE=interpret`, any `*_spec.spl`): a table read
(`DatabaseStoragePortV1.read_table` / `sqlite_format_read_table_bytes`) aborts the whole file with
`error: semantic: invalid operation: tuple index access on non-tuple type i64` (`executed=0`).
Production Messenger verbs hit it too.

Isolation (all seconds-long, on plaintext images; the slow decrypt was irrelevant):
- Read of a file-read or push-built `[u8]` image works, direct and through `port.read_table`.
- The same spec fails as soon as it has `use std.common.json.value.{JsonValue}` or `{json_value_field}`
  (either item alone); removing the import makes it pass. The module is named `value`.
- Site: `src/lib/nogc_sync_mut/database/sqlite_format/btree.spl` leaf branch,
  `val cell: (i64, [u8]) = match parse_table_leaf_cell(...): case Ok(value): value` then `cell.0`.
  The match-arm binding `value` resolves to the imported `value` module namespace instead of the payload,
  so `cell` is not the tuple. Renaming the binding to `decoded_pair` in btree.spl makes the read pass.
  The identical `Ok(value): value` pattern in cell.spl and record.spl was renamed too (same exposure).
  `cell` and `hdr` collisions: ruled out (renaming only the `value` binding fixes it).

Fix: the three renames above. Verified: `dense_storage_rows_spec.spl` 8/8 on the seed.
Class of bug: any `case Ok(value): value` in `src/lib` is exposed when a program also imports a module named `value`.
