# SCV: `scv_text_to_u8` returned all-zero bytes — every text-derived id collided by length (2026-08-26)

**Status:** FIXED in `src/lib/scv/store.spl` (`scv_text_to_u8` now uses `text.bytes()`); the
underlying seed defect is OPEN.

## Symptom
`scv_hash_text(prefix, value)` (chunk ids from merges, `file_*`, `conflict_*`, `syntax_node_*`,
`tree_*`, commit/op ids) hashed `scv_text_to_u8(value)`, whose loop
`for ch in value: out.push((ch.to_i64() & 0xFF).to_u8())` yields **0 for every character** on the
current Rust seed (`bin/release/x86_64-unknown-linux-gnu/simple`, probed 2026-08-26:
`scv_text_to_u8("one") == [0,0,0]`, `scv_hash_text("x","one") == scv_hash_text("x","ONE")`).
Consequences observed:
- `scv_syntax_node_changed_positions` saw no per-line change, so line/syntax merges returned the
  BASE text as "merged" and never produced a conflict (`scv_merge_spec` 5/5 red, `merged=one|two|three`
  instead of `ONE|two|THREE`).
- merged chunk ids collided with unrelated chunks of the same length; `export-tree` then failed with
  `ERROR corrupt chunk: sha256_e7ec…`.

## Reproduce (pre-fix red, post-fix green)
- `test/integration/app/scv_identity_merge_spec.spl` case 1 (`moved=ONE|two|THREE|`)
- `test/integration/app/scv_merge_spec.spl` "line-merges disjoint same-file edits" and
  "records divergent same-file merge conflicts as data"

## Fix
`scv_text_to_u8(value) -> value.bytes()` (verified `sha256("one")` matches `sha256sum`). merge.spl
additionally stages merged text to a file and chunks it via `scv_write_chunk_from_file`, so the
chunk id is always the digest of the bytes on disk (one digest path).

## Still open (not SCV's to fix)
- Seed/runtime: iterating a `text` with `for ch in value` and calling `ch.to_i64()` returns 0. Any
  other stdlib code using that idiom is silently wrong. Needs a runtime reproduce spec + fix.
- Object ids in repositories created before this fix are length-collided; `fsck`/`rebuild-db` on
  such repos will report corruption. No migration written (SCV is pre-cutover).
