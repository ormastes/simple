# SCV Workstream E (Pack): PROD-006 Research Findings

**Scope**: Production delta pack chains — bounded delta chains over content-defined chunks,
pack verify validates base/delta references, pack read limits chain depth, GC keeps reachable
bases, large edited files compress better than whole-object gzip packs.

---

## 1. Current Pack Architecture

**File**: `src/lib/scv/pack.spl` (465 lines)

Pack write (`scv_pack_write`, line 61) is a single-shot whole-snapshot operation:
1. Iterates all loose objects of every kind: `chunks/files/trees/commits/changes/operations/conflicts/syntax`
2. Builds a manifest (`format: scv-pack-v1\n`, then `kind|id|size|path` rows, `|`-separated)
3. Serialises a payload (`format: scv-pack-payload-v1\n`, then `entry kind id size\n<raw bytes>\nendentry\n`)
4. Gzip-compresses the entire payload and writes `<pack_id>.pack.gz` + `<pack_id>.manifest`
5. Pack id is `scv_hash_text("pack", manifest)`

**No concept of incremental, base, or delta packs exists today.** Every pack is a complete
snapshot of all loose objects at that point in time.

Pack verify (`scv_pack_verify_dir`, line 180) validates:
- Manifest row count equals payload entry count
- Object hash matches declared id for every entry
- No duplicate entries, no extra manifest fields, no absolute paths

Pack import (`scv_pack_import_payload`, line 297) unpacks entries to loose object paths;
`scv_pack_import_entry` (line 274) validates hash on intake.

Import path via: `std.common.compress.gzip.{gzip_compress, gzip_decompress}`.

---

## 2. GC and Maintenance Model

**File**: `src/lib/scv/maintenance.spl` (397 lines)

Reachability walk (`scv_reachable_object_ids`, line 333) traces from the current commit
through commits → trees → file objects → chunks → syntax nodes + parser index + views.

GC prune (`scv_gc_prune`, line 388) deletes unreachable loose objects in kinds:
`chunks`, `files`, `trees`, `commits`, `syntax`.

**Critical gap**: GC does NOT enumerate or inspect `.scv/objects/packs/`. Pack files are
never walked for reachability and are never pruned. For PROD-006's "GC keeps reachable
bases" requirement, pack-level reachability + base-pack pinning is entirely net-new work.

---

## 3. Available Compression Primitives

**Simple stdlib at**: `src/lib/nogc_sync_mut/compression/`

| Codec   | Path                                        | Status          |
|---------|---------------------------------------------|-----------------|
| gzip    | `compression/gzip/__init__.spl`             | In use by pack  |
| brotli  | `compression/brotli.spl` + `brotli/mod.spl` | Available       |
| lz4     | `compression/lz4.spl`                       | Available       |
| snappy  | `compression/snappy.spl`                    | Available       |
| zlib    | `compression/zlib.spl`                      | Available       |
| **zstd**| —                                           | **Not present** |

Gzip API exported from `__init__.spl`: `gzip_compress(data: [u8], level: i64) -> [u8]`,
`gzip_decompress(data: [u8]) -> [u8]?`, plus `gzip_compress_best/fast/default`.

**Key constraint**: The acceptance criterion "large edited files compress better than
whole-object gzip packs" cannot be achieved by swapping compression codec (zstd is absent).
The compression win must come from **delta encoding**: storing only the diff between a new
chunk and a base chunk will be far smaller than re-gzipping the whole object each time.

---

## 4. Delta Chain Design Requirements

**No PROD-006 delta pack design exists in `doc/05_design/scv.md`.**
Implementation Slices stop at Slice 5 (parser registry). The design doc covers
content-defined chunks at the object layer (whole-file + part chunks for large files) but
has no specification for delta packs at the archival layer. The implementing workstream
must produce this design.

**From domain research** (`doc/01_research/domain/scv.md`):
- Git pack format uses `ofs-delta` and `ref-delta` entry types; FastCDC is the recommended
  CDC baseline (gear-hash, lower rolling-hash overhead than Rabin).
- SCV implication recorded in research: use content-addressed chunks and Merkle DAG/rope
  structure for deduplication; pack compression is a maintenance layer, not the identity model.
- FastCDC targets natural chunk boundaries so that small edits produce one new chunk rather
  than invalidating the whole file.

**Derived requirements for PROD-006** (not yet designed):
- New entry type: `entry-delta kind id base_id delta_size` + delta bytes + `endentry`
- Chain depth field or index needed at verify-time to enforce depth limit
- Base entries must be in the same pack or a referenced prior pack; verify must resolve the full chain
- Manifest schema must version-bump (`scv-pack-v2`) or delta rows extend v1 with backward
  compatibility path; current strict parser rejects extra fields so in-place extension is unsafe
- `scv_pack_read` (does not yet exist) must cap chain depth and return error on cycles or
  overlong chains

---

## 5. Constraints and Risks

| Risk | Detail |
|------|--------|
| No delta algorithm in stdlib | Neither xdelta, bsdiff, nor rolling-hash diff exists; must implement or use FFI to system diff |
| GC pack gap | Pack files are invisible to current GC; base-pack pinning must be added before GC runs on any repo with delta packs |
| Manifest v1 strict parser | `scv_pack_payload_matches_manifest_bytes` rejects any row with extra fields; delta entries need a versioned format path |
| No `scv_pack_read` | Read-by-id from a pack (following delta chain) is absent; whole pack is currently decompressed on every verify |
| CDC chunking not integrated with pack layer | `scv_pack_payload_for_kind` packs whole loose objects; CDC part-chunks are stored as loose objects, not sub-object deltas |
| No chain-depth index | Enforcing a bounded depth requires an index or inline header; neither exists |
| Single-threaded gzip over entire payload | For large repos, full-payload gzip on every pack-write is the current bottleneck; delta packs reduce payload size but not the O(n) scan cost |

---

## 6. Specific File Paths Referenced

| File | Role |
|------|------|
| `src/lib/scv/pack.spl` | Pack write/verify/import (465 lines) |
| `src/lib/scv/maintenance.spl` | GC prune, reachability, stats (397 lines) |
| `src/lib/nogc_sync_mut/compression/gzip/__init__.spl` | gzip API (compress/decompress) |
| `src/lib/nogc_sync_mut/compression/lz4.spl` | lz4 (available) |
| `src/lib/nogc_sync_mut/compression/brotli.spl` | brotli (available) |
| `doc/05_design/scv.md` | Design doc — no delta pack section |
| `doc/01_research/domain/scv.md` | Domain research — FastCDC, Git pack, IPFS |
| `test/integration/app/scv_pack_import_spec.spl` | Import + private-sync tests |
| `test/integration/app/scv_pack_verify_safety_spec.spl` | Verify safety rejection tests |

---

## 7. Implementation Approach Recommendations

**Option A — Shallow delta in the pack payload (Git-style)**
Add `entry-delta` rows alongside `entry` rows in a new `scv-pack-payload-v2` format.
Verify walks `entry-delta` records, resolves `base_id` within the same pack, enforces a
configurable depth cap (e.g. 10). GC must track all base ids in packed packs as pinned.
- Pro: minimal format change, pure-Simple delta algorithm can start with byte-diff
- Con: requires delta algorithm implementation; verify becomes O(chain_depth) per entry

**Option B — Separate delta packs referencing base packs**
Base pack contains full objects; delta pack contains diffs and a `base_pack:` header.
- Pro: simpler chain: at most one level of indirection per pack
- Con: cross-pack references complicate portability; private-sync must transfer both packs

**Option C — Delta at the chunk layer only**
Delta-encode only `chunks/` objects (binary content), leave metadata objects (files, trees,
commits) as full objects. Reduces scope since metadata is small.
- Pro: safe: metadata verify logic unchanged; delta only where compression win is large
- Con: requires CDC boundary stability across versions to avoid delta explosion

**Recommended first step**: Design the `scv-pack-payload-v2` format (manifest row schema for
delta entries, chain-depth header) before writing any code. The format decision drives all
downstream verify, import, GC, and read changes.
