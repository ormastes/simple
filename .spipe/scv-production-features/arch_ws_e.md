# SCV Workstream E: PROD-006 Delta Pack Chain Architecture

## 1. Module List

| File | Change |
|------|--------|
| `src/lib/scv/delta.spl` | **NEW** — rolling-hash delta encode/decode |
| `src/lib/scv/pack.spl` | **MOD** — v2 payload writer, v2 verify, pack read with chain resolution |
| `src/lib/scv/maintenance.spl` | **MOD** — GC pack reachability walk, base pinning |

---

## 2. Key Interfaces

### delta.spl — Delta encoding

```
# Compute a binary delta from base → target using rolling-hash copy/insert instructions.
# Returns delta bytes or error text.
fn scv_delta_encode(base: [u8], target: [u8]) -> ([u8], text)

# Reconstruct target by applying delta bytes onto base.
# Returns reconstructed bytes or error text.
fn scv_delta_decode(base: [u8], delta: [u8]) -> ([u8], text)

# Max chain depth enforced at verify and read time.
val SCV_DELTA_MAX_DEPTH: i64 = 10
```

Delta wire format (little-endian, binary):
```
[u32 magic=0xDELT] [u32 base_size] [u32 target_size]
{ opcode: u8
    0x01 COPY  [u32 offset] [u32 length]   -- copy from base
    0x02 INSERT [u16 length] [bytes...]    -- literal insert
}
[u32 crc32 over all preceding bytes]
```

### pack.spl — Pack v2 payload schema

Payload text header: `format: scv-pack-payload-v2\n`

Full-object row (unchanged from v1):
```
entry <kind> <id> <byte_size>
<raw_bytes>
endentry
```

Delta row (new):
```
entry-delta <kind> <id> <base_id> <chain_depth> <delta_byte_size>
<delta_bytes>
endentry
```

Constraints:
- `base_id` must reference an `entry` or `entry-delta` row earlier in the same payload
- `chain_depth` is the resolved depth from the nearest full `entry` ancestor (1 = direct delta off a full object)
- `chain_depth` must be ≤ `SCV_DELTA_MAX_DEPTH`

### pack.spl — Pack write v2

```
# Write a v2 pack: groups objects by kind, attempts delta for chunks/ objects,
# falls back to full entry if delta is larger or base not found.
fn scv_pack_write_v2(root: text, pack_id: text, kind_filter: text?) -> text

# Low-level: produce the v2 payload bytes (full + delta entries).
fn scv_pack_payload_v2(objects: [(text, text, [u8])]) -> [u8]
```

### pack.spl — Pack verify v2

```
# Verify a v2 pack: validates all entry and entry-delta rows,
# resolves each delta chain, checks chain_depth header values,
# returns (error_or_ok, checked_count, delta_count, max_chain_depth).
fn scv_pack_verify_v2(pack_dir: text, pack_id: text, label: text)
    -> (text, i64, i64, i64)
```

Verify algorithm:
1. Parse payload sequentially; build `seen: map<id, (kind, depth)>`
2. For each `entry-delta`: look up `base_id` in `seen`; compute depth = `base_depth + 1`; reject if depth > MAX or cycle detected
3. Hash-check: decode delta → reconstruct → verify content hash

### pack.spl — Pack read v2 (new)

```
# Read a single object from a v2 pack by kind+id; resolves delta chain up to MAX_DEPTH.
# Returns raw object bytes or error.
fn scv_pack_read_object(pack_dir: text, pack_id: text, kind: text, id: text)
    -> ([u8], text)
```

---

## 3. Data Flow

**Write path**
```
loose objects (chunks/) → similarity grouping (rolling hash fingerprints)
  → scv_delta_encode(base_blob, target_blob)
  → entry-delta rows in v2 payload
  → gzip_compress(payload) → pack_id.pack.gz
  → manifest v2 (entry + entry-delta rows)
```

**Read / reconstruct path**
```
scv_pack_read_object(kind, id)
  → locate pack containing id via manifest index
  → parse payload sequentially; collect chain [id → base_id → … → full_entry]
  → apply scv_delta_decode iteratively from base outward
  → verify reconstructed hash == id
```

**GC path (maintenance.spl)**
```
scv_reachable_object_ids(root)           # existing: traces commit graph
  + scv_pack_reachable_base_ids(root)    # NEW: enumerate base_ids in all packs
  → union of reachable ids
scv_gc_prune(root, reachable)            # existing logic
scv_gc_prune_packs(root, reachable)      # NEW: delete packs where all objects unreachable
                                         #      but NEVER delete a pack whose base_id is reachable
```

---

## 4. Delta Algorithm Choice

**Rolling-hash copy/insert (xdelta-lite variant)**

Rationale:
- FastCDC gear-hash already identifies stable chunk boundaries at the CDC layer; the delta
  algorithm needs only to diff two same-kind `chunks/` blobs that differ by a small edit
- A sliding-window hash (32-byte window, Adler-32 rolling sum) is ~50 lines of Simple and
  has no stdlib dependency
- xdelta/bsdiff require suffix arrays (complex); brotli/snappy are whole-blob codecs, not
  structural diffs
- For metadata objects (files, trees, commits) — which are small SDN text — store as full
  `entry` rows; delta only applies to `chunks/` binary content where size wins are largest

**Not chosen**: bsdiff (suffix array complexity), cross-pack references (Option B, portability risk), full-file CDC layer delta (Option C, boundary stability fragile across format versions).

---

## 5. File Ownership (Disjoint)

| File | Owns |
|------|------|
| `src/lib/scv/delta.spl` | `scv_delta_encode`, `scv_delta_decode`, `SCV_DELTA_MAX_DEPTH`, wire format constants |
| `src/lib/scv/pack.spl` | `scv_pack_payload_v2`, `scv_pack_write_v2`, `scv_pack_verify_v2`, `scv_pack_read_object`, v2 manifest parsing |
| `src/lib/scv/maintenance.spl` | `scv_pack_reachable_base_ids`, `scv_gc_prune_packs`, integration into existing `scv_reachable_object_ids` + `scv_gc_prune` |
