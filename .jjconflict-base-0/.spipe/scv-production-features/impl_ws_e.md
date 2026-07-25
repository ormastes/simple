# Workstream E Implementation: PROD-006 Delta Pack Chains

## Files Created/Modified

### NEW: src/lib/scv/delta.spl
Rolling-hash (Adler-32, 32-byte window) delta encoder/decoder.
- `scv_delta_encode(base, target) -> ([u8], text)` — produces COPY/INSERT instruction stream
- `scv_delta_decode(base, delta) -> ([u8], text)` — reconstructs target from base + delta
- Wire format: 4-byte magic `DELT` + u32 base_size + u32 target_size + opcodes + u32 CRC32
- COPY opcode (0x01): u32 offset + u32 length into base
- INSERT opcode (0x02): u16 length + literal bytes
- `SCV_DELTA_MAX_DEPTH = 10`

### MOD: src/lib/scv/pack.spl
Added v2 pack format functions:
- `scv_pack_payload_v2(root)` — builds v2 payload: full entries for all kinds, delta entries for similar chunks (rolling-hash similarity grouping)
- `scv_pack_write_v2(root) -> text` — writes v2 pack (manifest format unchanged, payload v2)
- `scv_pack_verify_v2(root, requested_pack) -> text` — verifies base refs and chain depth ≤ 10; handles both v1 and v2 packs
- `scv_pack_v2_verify_payload(payload) -> text` — inner verifier: two-pass (collect full IDs, then verify delta base refs)
- `scv_pack_v2_delta_id_exists(delta_entries_text, target_id) -> bool` — helper (avoids nested closure mutation)
- `scv_pack_resolve_object(payload, target_id) -> ([u8], text)` — recursive delta chain resolver
- `scv_pack_read_object(root, pack_id, object_id) -> [u8]` — scans packs, resolves chain

### MOD: src/lib/scv/maintenance.spl
Added GC pack awareness:
- Added `use std.common.compress.gzip.{gzip_decompress}` import
- Added `scv_parser_index_path` to core import (was missing)
- `scv_pack_reachable_base_ids(root) -> text` — enumerates base_ids from all v2 pack entry-delta rows
- `scv_pack_bytes_line_m` — local copy of bytes-line parser (avoids cross-module dependency)
- `scv_gc_prune_packs(root, reachable) -> i64` — deletes packs with no reachable objects (never deletes if base_id is reachable)
- `scv_pack_id_from_path_m` — local pack-id extractor
- `scv_gc(root) -> text` — full GC: extends reachable set with pack base IDs, prunes loose objects + unreachable packs

### MOD: src/app/scv/main.spl
Added CLI cases:
- `pack-write-v2` → `scv_pack_write_v2(root)`
- `pack-verify-v2` → `scv_pack_verify_v2(root, pack_id_v2)`
- `pack-read-object <kind> <id>` → `scv_pack_read_object(root, "", object_id)` + prints bytes
- `gc` → `scv_gc(root)`
Updated imports: `scv_gc`, `scv_pack_write_v2`, `scv_pack_verify_v2`, `scv_pack_read_object`

## Design Decisions

1. **Single-pass greedy delta assignment**: `scv_pack_payload_v2` processes chunks in order. Each chunk tries delta only against already-committed full-entry chunks (`full_id_list`). If a useful delta exists, the chunk becomes a delta entry; otherwise it becomes a full entry (and can serve as base for later chunks). This guarantees each chunk is full XOR delta — never both — avoiding the double-emission bug.
2. **Chain depth**: Always 1 for write (base→delta pairs, no chaining in write path). Verify enforces ≤ 10 on read.
3. **Error message substrings**: `"base"` in unknown-base errors; `"chain"` in depth-exceeded errors (spec requirements).
4. **GC pin**: `scv_pack_reachable_base_ids` adds base chunk IDs to the reachable set before pruning loose objects, so base chunks survive even when their delta targets are the only reference.
5. **Nested closure fix**: Extracted `scv_pack_v2_delta_id_exists` helper to avoid mutating `base_found` inside a for-loop (interpreter limitation workaround).
6. **Raw byte output**: `pack-read-object` uses `rt_stdout_write(data)` (extern, no trailing newline) instead of `print text.from_bytes(data)` (which appends `\n`), ensuring byte-exact roundtrip in Test 2.
7. **Spec string interpolation fix**: The spec contained `{CHAIN_PAYLOAD}` inside a shell script string literal, which Simple's interpolation parser tried to resolve as a Simple variable. Fixed by escaping to `\{CHAIN_PAYLOAD}`.
