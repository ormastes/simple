# NVFS (SimpleFS-NV) Design — Version 3

> **Supersedes delta:** This document is a **delta to v2** (`doc/05_design/nvfs_design_v2.md`).
> Only new or changed sections are described here. Readers must have v2 in hand; v3 does
> not re-describe what v2 covers. All v2 sections not mentioned here are unchanged.
>
> **Adds milestones:** N7a (inline compression), N7b (inline deduplication). These split
> and extend the v2 N7 milestone (native encryption + raw send), which is now renamed
> N7c in the phased table (§V3-6).
>
> **Related designs (cross-refs, unchanged from v2):**
> - `doc/05_design/fs_driver_interface.md`
> - `doc/05_design/nvfs_posix_wrapper.md`
> - `doc/05_design/nvfs/svllm_requirements.md`
> - `doc/05_design/nvfs/from_spostgre.md`
> - `doc/05_design/spostgre_design.md`
>
> **Status:** Forward-looking design (not yet implemented). 2026-04-18.

---

## V3-1. Scope delta vs v2

v2 left two capabilities marked "future" in the Capability table (§19): `Compress` and
the inline variant of `Dedup`. v3 specifies both as new sub-milestones, plus the
interaction rules with v2's N7 encryption layer.

| Change area | v2 | v3 |
|---|---|---|
| Compression | not designed | N7a: per-dataset LZ4/Zstd, class-aware (§V3-2) |
| Dedup | offline-only daemon (§8) | N7b: inline hash-table DDT + class policies (§V3-3) |
| Encryption ordering | plaintext blocks | compress-then-encrypt ordering enforced (§V3-4) |
| Dedup + encryption | not addressed | plaintext-hash dedup key, per-dataset dedup key (§V3-4) |
| Pmap entry | 80 bytes (v2) | 88 bytes: adds `compress_algo` + `compressed_len` (§V3-5) |
| Superblock magic | `b"NVFS0002"` | `b"NVFS0003"` (new incompat flag) |
| Milestones | N1–N8 | N1–N8, N7 split into N7a/N7b/N7c (§V3-6) |

---

## V3-2. Compression layer (N7a)

### V3-2.1 Design goals

Compression is **per-dataset, per-arena, opt-in**. It follows the ZFS model: the
filesystem decides at write time whether to compress a block; the on-disk format records
the algorithm and compressed length in the extent pointer so the reader can decompress
transparently without any extra seek.

Compression is **not** applied uniformly. NVFS is storage-class-aware:

| Storage class | Default compression | Rationale |
|---|---|---|
| `META_DURABLE` | None | Metadata blocks are small, random-access, latency-sensitive; compress overhead not worth it |
| `DB_WAL` | None | Sequential log; appends must be as fast as possible; incompressible in practice |
| `DB_TEMP` | LZ4 | Ephemeral; space saving with negligible latency budget |
| `MODEL_IMMUTABLE` | None | ML weight tensors are already dense (float16/bfloat16); compress ratio ≈ 1.0; overhead wasted |
| `GENERAL_MUTABLE` | Zstd-3 | General files benefit most; default Zstd level 3 balances ratio vs CPU |
| `CHECKPOINT_SNAPSHOT` | LZ4 | Snapshots are read-rarely; fast compress on write, fast decompress on restore |

Per-dataset override: mount option `compress=<algo>:<class>` overrides the default.
`compress=none` disables all compression for a dataset. Per-file xattr `nvfs.compress`
overrides per-dataset setting.

### V3-2.2 Supported algorithms

| Tag | Name | Typical ratio | Notes |
|---|---|---|---|
| `0` | None | 1.0 | No-op; v2 default |
| `1` | LZ4 | 1.5–2.5× | ~3 GB/s compress, ~5 GB/s decompress; good for DB_TEMP + snapshots |
| `2` | Zstd-3 | 2.5–4× | ~500 MB/s compress, ~1.5 GB/s decompress; good for GENERAL_MUTABLE |
| `3` | Zstd-19 | 4–6× | ~30 MB/s compress; offline archival only; not for hot paths |

Comparison with reference filesystems:

| Algorithm | ZFS default? | Btrfs default? | NVFS default? |
|---|---|---|---|
| LZ4 | Yes (lz4) | Yes (lz4) | Yes, for DB_TEMP + snapshots |
| Zstd | Optional (`compress=zstd`) | Optional (`compress=zstd`) | Yes, GENERAL_MUTABLE |
| Gzip | Optional (gzip-1..9) | Optional (zlib) | Not supported (patent-free alternatives sufficient) |
| LZMA/XZ | No | Optional (xz) | Not supported (too slow for NVMe latency targets) |

NVFS omits gzip and LZMA: NVMe latency targets (< 100 µs end-to-end for metadata reads)
rule out slow compressors on hot paths.

### V3-2.3 Compressed-extent descriptor

A compressed extent is described in the pmap entry (§V3-5). The extent data on disk
is laid out as:

```
compressed_extent_block:
  compressed_data: [u8; compressed_len]   # raw LZ4 / Zstd stream
  # No padding within the compressed block; the next block starts at
  # physical_offset + compressed_len (aligned to 512B sector boundary).
```

The `decompressed_len` is the logical block size (always a power of two; default 4096 B).
It is not stored explicitly — the reader derives it from the logical page size stored in
the superblock `default_block_size` field.

**Incompressible detection:** if compressed output ≥ 0.9 × raw size, NVFS stores the
raw block and sets `compress_algo = 0` (None) in the pmap entry for that extent.
This avoids the overhead of storing "compressed" data that is larger than the original.

### V3-2.4 Read/write path

**Write path (compressed):**
1. Caller issues `arena_append(data)`.
2. NVFS checks `compress_algo` for the target arena's dataset.
3. If algo ≠ None: compress `data` → `cdata`. If `len(cdata) >= 0.9 * len(data)`, fall back to algo = None.
4. Write `cdata` (or `data`) to the physical device at the next free sector boundary.
5. Record `compress_algo` + `compressed_len` in the new pmap entry.
6. Commit transaction (CoW B-tree update, §2 of v2).

**Read path (decompressed):**
1. Caller issues `arena_read(logical_page_no)`.
2. NVFS looks up the pmap entry; reads `compress_algo` + `compressed_len`.
3. If `compress_algo = 0`: read raw block, return directly.
4. Else: read `compressed_len` bytes, decompress to `default_block_size` bytes, verify
   Merkle checksum of the **compressed** bytes (checksum is over ciphertext when
   encryption is enabled — see §V3-4), return decompressed data.

### V3-2.5 ARC interaction

The ARC cache (v2 §13) stores **decompressed** blocks in memory. Storing compressed
blocks in ARC would require per-entry decompression on every cache hit, trading CPU for
RAM. At NVFS's target ARC sizes (< 25% of process RSS), the RAM savings of compressed
ARC are not worth the CPU overhead on NVMe hardware. A future `arc_compress=on` mount
option may revisit this for memory-constrained deployments.

---

## V3-3. Deduplication layer (N7b)

### V3-3.1 Design goals

v2 §8 describes an **offline** deduplication daemon (comparable to `duperemove`). v3
adds an **inline** dedup path backed by a content-addressable hash table (DDT —
Deduplication Table), modelled on OpenZFS's DDT. Inline dedup eliminates the second
write of duplicate blocks, at the cost of hash computation on every write and RAM for
the DDT.

Inline dedup is **off by default** for all storage classes. It is **opt-in per dataset**
via mount option `dedup=on` or xattr `nvfs.dedup=on` on a subvolume.

### V3-3.2 Storage class policies

| Storage class | Dedup opt-in? | Rationale |
|---|---|---|
| `META_DURABLE` | Never (forced off) | Metadata blocks are unique by construction (generation counter in every node); dedup would waste CPU |
| `DB_WAL` | Never (forced off) | WAL entries carry monotonically increasing LSNs; no duplicate content |
| `DB_TEMP` | Never (forced off) | Explicitly opts out — ephemeral data; dedup overhead with zero benefit |
| `MODEL_IMMUTABLE` | Aggressive (forced on when dataset dedup=on) | Shared weight tensors across fine-tuned model variants; high duplicate content expected |
| `GENERAL_MUTABLE` | Opt-in | General files benefit when dedup=on; off by default to avoid latency regression |
| `CHECKPOINT_SNAPSHOT` | Opt-in | Snapshots of similar data often share blocks; opt-in when space savings matter |

### V3-3.3 DDT layout

The DDT is a hash table mapping:

```
content_hash (u8[32]) → DedupEntry
```

```
struct DedupEntry:
    content_hash: [u8; 32]    # Blake3 hash of decompressed plaintext block
    physical_ref: u64          # pmap logical_page_no of the canonical stored block
    birth_gen: u64             # generation when first stored (for GC)
    refcount: u32              # number of logical blocks sharing this physical block
    flags: u8                  # bit0=pinned (MODEL_IMMUTABLE), bit1=verified
    _pad: [u8; 3]
```

Total: 56 bytes per entry. A 10 GiB DDT holds ~190M entries — sufficient for ~1 PiB of
4 KiB blocks at 50% dedup ratio.

**DDT storage:** The DDT is stored in a new B-tree:

| Tree | Objectid constant | Purpose |
|---|---|---|
| Dedup tree | `DEDUP_TREE_OBJECTID = 12` | DDT: content_hash → DedupEntry |

The dedup tree is appended to the v2 ten-tree forest (§2 of v2), making an eleven-tree
forest in v3. The dedup tree root is recorded in the superblock (new field
`dedup_root_lba`).

**DDT RAM cache:** The DDT is too large to hold entirely in RAM for large filesystems. A
two-level scheme is used:

- **Hot DDT:** In-memory hash table, sized to `dedup_cache_mb` mount option (default
  256 MB). Entry eviction is LRU. On miss, fall through to the on-disk dedup tree.
- **Cold DDT:** The on-disk dedup B-tree. Lookups are O(log n) B-tree reads.

### V3-3.4 Write path with inline dedup

```
arena_append(data):
  1. If dedup disabled for this arena's class: skip to step 6.
  2. Compute Blake3(plaintext_data) → hash.
  3. Lookup hash in hot DDT. On hit: refcount++ → return the existing logical_page_no.
     Return immediately (no data written to device).
  4. On miss: lookup hash in cold DDT (B-tree read).
     On hit: load into hot DDT, refcount++ → return existing logical_page_no.
  5. On miss in both: proceed to step 6 (new block).
  6. Compress data if compress_algo ≠ None (§V3-2.4).
  7. Encrypt compressed data if encryption enabled (§V3-4).
  8. Write ciphertext/compressed/raw block to device.
  9. Insert new DedupEntry(hash, new_logical_page_no, birth_gen, refcount=1) into
     hot DDT + dedup B-tree.
  10. Update pmap entry with compress_algo + compressed_len.
  11. Commit transaction.
```

**Reflink integration:** When dedup finds a match (steps 3–4), the match is implemented
via the existing reflink machinery (v2 §7): SHARED_DATA_REF backref is added to the
extent tree, refcount is incremented, and the calling inode's EXTENT_DATA item points
at the shared physical block. No new on-disk mechanism is needed beyond the DDT.

### V3-3.5 Trade-off analysis

| Dimension | Pro | Con |
|---|---|---|
| Write amplification | **Reduced** when dedup hits (skip device write entirely) | **Increased** when dedup misses: extra B-tree write for DDT entry + hash computation |
| Space savings | High for MODEL_IMMUTABLE (shared weight tensors, 2–10× savings) | Minimal for DB_WAL, META_DURABLE (near-zero dedup ratio) |
| Latency (dedup miss) | No change | +hash compute time (~1 µs/4KiB Blake3 on x86_64 AVX2) + DDT lookup |
| Latency (dedup hit) | Device write eliminated; reflink is metadata-only | DDT lookup (hot=hash table O(1); cold=B-tree O(log n)) |
| RAM | Hot DDT configurable (default 256 MB) | Large DDT = large working set; memory pressure on constrained hosts |
| Crash consistency | DDT B-tree is CoW-consistent (same as all other trees) | DDT B-tree adds to transaction commit overhead |
| GC complexity | DedupEntry.refcount decremented on unlink/CoW; entry freed at refcount=0 | Reference counting is error-prone; requires comprehensive tests (comparable to delayed-ref queue §5 of v2) |

**When to enable:** MODEL_IMMUTABLE datasets with shared fine-tuned weight tensors are
the primary intended beneficiary. GENERAL_MUTABLE datasets with known duplicate content
(backup archives, container image layers) are a secondary use case.

**When not to enable:** DB_WAL, META_DURABLE, and DB_TEMP must never be deduplicated
(class policy forces off). Enabling dedup on GENERAL_MUTABLE without profiling the
workload's dedup ratio is not recommended — the write-path overhead is always paid, but
the space benefit is workload-dependent.

---

## V3-4. Interaction with encryption (N6a/N7c)

The ordering of compression, deduplication, and encryption is load-bearing. The wrong
ordering breaks either dedup correctness or security.

### V3-4.1 Ordering rule

```
plaintext → [dedup-hash] → compress → encrypt → on-disk ciphertext
```

**Compression before encryption (mandatory):** Ciphertext is indistinguishable from
random data; it cannot be compressed. Compressing after encrypting yields ratio ≈ 1.0
and wastes CPU. Compression must occur on plaintext before encryption.

**Dedup hash on plaintext (mandatory for correctness):** The DDT key is the Blake3 hash
of the **plaintext** (before compression, before encryption). This ensures that two
blocks with identical plaintext deduplicate regardless of:
- Which DEK encrypted them (different datasets with different keys still dedup).
- What compression algorithm was applied (dedup precedes compression in the pipeline).

This matches OpenZFS's dedup-on-plaintext model.

**Security implication:** Hashing plaintext before encryption means an attacker who can
manipulate writes and observe DDT behaviour can learn whether two blocks have the same
content (the "guess-and-check" DDT oracle attack). This is a known trade-off accepted by
ZFS and most production dedup systems. For datasets where this is unacceptable, dedup
must be disabled (class policy for META_DURABLE/DB_WAL already forces it off).

### V3-4.2 Key hierarchy changes

v2 §14 defines a three-level key hierarchy: user key → wrapping key → master key (per-dataset) → per-block DEK (derived from master key + block address + IV).

v3 adds a **dedup-hash key (DHK)** at the dataset level:

```
User key (passphrase / key manager)
  → wrapping key (per-volume)
    → master key (per-dataset)
      → dedup-hash key (per-dataset, derived from master key + constant "dhk")
        → HMAC(DHK, plaintext_block) used as DDT key instead of Blake3(plaintext)
      → per-block DEK (derived from master key + block address + IV)
```

Using HMAC(DHK, plaintext) instead of Blake3(plaintext) as the DDT key means an attacker
who reads the on-disk DDT cannot reverse the hash to the plaintext without the DHK. The
DDT key is dataset-scoped: blocks from different datasets with different DHKs do not
dedup against each other, even if their plaintext is identical. This is a privacy
trade-off (less cross-dataset dedup) for a security gain (DDT does not leak plaintext
identity across dataset boundaries).

### V3-4.3 Compressed + encrypted on-disk layout

The on-disk block for a compressed+encrypted extent:

```
on_disk_block:
  iv: [u8; 12]                      # 96-bit IV (deterministic, from master_key_id + obj + off)
  ciphertext: [u8; compressed_len]  # AES-256-GCM ciphertext of compressed data
  auth_tag: [u8; 16]                # GCM auth tag over (iv + ciphertext)
```

The Merkle checksum (pmap entry `checksum` field) is computed over `(iv + ciphertext +
auth_tag)` — i.e., over the **ciphertext**, not the plaintext. This is consistent with
the v2 §14.4 threat model (checksums are in plaintext; an attacker can verify block
integrity without decrypting, but cannot read content).

### V3-4.4 Raw send interaction

`nvfs send --raw` (v2 §10.3) emits ciphertext bytes. When compression is enabled, the
emitted bytes are compressed-then-encrypted (as stored). The receiver does not need to
know the compression algorithm — it stores the ciphertext opaquely. When the receiver
mounts with the correct key, the decrypt → decompress pipeline is driven by the
`compress_algo` field in the pmap entry (recovered from the stream's extent records).

---

## V3-5. Updated on-disk layout

### V3-5.1 Pmap entry (v3, 88 bytes)

The v2 pmap entry (80 bytes) is extended by 8 bytes: a `compress_algo` byte (reusing
the same enum as `checksum_algo`), a `compressed_len` u32, and 3 reserved pad bytes.

```
offset  size  field
0x00    8     logical_page_no (u64)
0x08    8     physical_arena_id (u64)
0x10    8     physical_offset (u64)
0x18    8     page_generation (u64)         # CoW generation (v1 retained)
0x20    8     birth_gen (u64)               # txg of first write (v2 §4)
0x28    1     checksum_algo (u8)            # ChecksumAlgo tag (v2 §3.2)
0x29    1     compress_algo (u8)            # NEW v3: CompressAlgo enum (§V3-2.2)
0x2A    2     reserved_algo_pad
0x2C    4     compressed_len (u32)          # NEW v3: length of compressed bytes on disk
                                            # 0 = not compressed (compress_algo = None)
0x30    4     flags (u32)                   # bit0=blob_pointer, bit1=evicted (v1/v2 bits)
0x34    4     reserved_flags_pad
0x38    32    checksum (u8[32])             # Merkle checksum of target (v2 §3)
```

Total: 88 bytes. Note: the v2 `flags` field has been moved from 0x2C to 0x30 to
accommodate `compressed_len`. Migration from v2 (80-byte entry) requires an offline
conversion step (see §V3-7).

### V3-5.2 Dedup-tree superblock fields (new)

```
struct NvfsSuperblock (additions to v2 §17.1):
  ...
  0x68    8     dedup_root_lba (u64)    # NEW v3: root of dedup B-tree
  0x70    8     dedup_root_gen (u64)    # NEW v3: generation of dedup tree root
  0x78    1     dedup_enabled (u8)      # NEW v3: 0=off, 1=on (dataset-level)
  0x79    1     compress_default (u8)   # NEW v3: CompressAlgo for new extents
  0x7A    6     reserved_v3_flags
  ...
  magic: b"NVFS0003"                    # NEW v3 magic; distinguishes from v2
```

The v3 superblock is not forward-compatible with v2. Volumes with magic `b"NVFS0003"`
cannot be mounted by a v2 NVFS implementation. Volumes with magic `b"NVFS0002"` can be
mounted by a v3 implementation (backward-compatible read; compression and dedup features
are simply not present).

### V3-5.3 CompressAlgo enum

```
enum CompressAlgo:
    None   = 0   # No compression; compressed_len = 0
    LZ4    = 1   # LZ4 frame format; max block size = default_block_size
    Zstd3  = 2   # Zstd level 3
    Zstd19 = 3   # Zstd level 19 (offline archival only)
```

---

## V3-6. Updated milestones

The v2 N7 milestone (native encryption + raw send, 5 weeks) is split into three
sub-milestones to sequence the new features correctly.

### N7a — Inline compression (4 weeks, 2 eng)

- `CompressAlgo` enum + per-dataset `compress_default` mount option.
- Compress-on-write in `arena_append`: LZ4 and Zstd-3 paths, incompressible fallback.
- Decompress-on-read transparent to caller.
- Pmap entry v3 (88 bytes): `compress_algo` + `compressed_len` fields.
- Class-aware defaults table enforced at arena creation.
- ARC stores decompressed blocks (§V3-2.5).
- Superblock magic `b"NVFS0003"` + `compress_default` field.

**Acceptance:**
- LZ4 compression on GENERAL_MUTABLE: write throughput ≥ 80% of uncompressed (< 20%
  overhead on compressible data at full NVMe bandwidth).
- Zstd-3 on GENERAL_MUTABLE: on-disk size ≤ 45% of raw for synthetic text workload.
- MODEL_IMMUTABLE arena: compression skipped (class policy); no pmap entry overhead.
- Incompressible block (random data): stored uncompressed; no size regression.
- Round-trip: data written and read back byte-for-byte identical.

### N7b — Inline deduplication (6 weeks, 2 eng)

- Dedup B-tree (`DEDUP_TREE_OBJECTID = 12`): DDT as eleventh tree.
- `DedupEntry` struct (56 bytes) + hot DDT RAM cache (configurable, default 256 MB).
- Write path: Blake3/HMAC-DHK hash → DDT lookup → reflink on hit / insert on miss.
- Per-class dedup policy enforcement (META_DURABLE/DB_WAL/DB_TEMP forced off).
- Dedup-hash key (DHK) derivation from master key (§V3-4.2).
- Refcount GC: decrement on unlink/CoW; free DDT entry at refcount=0.
- Dedup tree root in superblock (`dedup_root_lba` field).

**Acceptance:**
- MODEL_IMMUTABLE dataset with 10 copies of the same 1 GiB weight tensor: on-disk usage
  ≤ 1.1 GiB (≥ 9× dedup ratio).
- DB_TEMP/META_DURABLE/DB_WAL arenas: dedup path not entered (class policy verified by
  test).
- Dedup miss overhead: ≤ 2 µs/4KiB write on warm DDT (hash compute + hot DDT lookup).
- Crash consistency: `nvfs check` after kill -9 during dedup-heavy write: no leaked
  extents, refcounts consistent.
- DDT GC: after deleting the 9 duplicate copies, used space returns to 1× weight tensor
  size (no leaked DDT entries; verified by `nvfs stats --dedup`).

### N7c — Native encryption + raw send (5 weeks, 2 eng)

*(Same as v2 N7, renamed to N7c to make room for N7a/N7b.)*

- AES-256-GCM encryption with three-level key hierarchy + DHK for dedup (§V3-4.2).
- Compress-then-encrypt ordering enforced (§V3-4.1).
- `nvfs send --raw` for encrypted raw send.
- `nvfs change-key` (rewrap only).
- `Capability::Encrypt` advertisement.
- SHA256 checksum algorithm option.

**Acceptance:** same as v2 N7, plus:
- Encrypted + compressed volume: read returns correct plaintext; on-disk size is
  compressed (not plaintext-size).
- Encrypted + dedup: two identical plaintext blocks deduplicate to one physical block;
  DDT key is HMAC-DHK, not raw Blake3 (verified by inspecting DDT tree on-disk).

---

## V3-7. Migration plan: v2 → v3

Migration is flag-gated and per-dataset opt-in. A v2 volume can be opened by a v3
implementation with no changes; compression and dedup features are simply unavailable
until the volume is upgraded.

### Step 1: Superblock upgrade (offline)

```
nvfs upgrade --volume=<dev>
```

- Reads v2 superblock (`b"NVFS0002"`).
- Extends all pmap entries from 80 bytes to 88 bytes (zero-fills new fields:
  `compress_algo=0`, `compressed_len=0`, `reserved=0`).
- Writes v3 superblock (`b"NVFS0003"`) with `dedup_root_lba=0` (empty dedup tree),
  `compress_default=0` (None), `dedup_enabled=0`.
- Creates an empty dedup B-tree root.
- The upgrade is atomic: if it fails mid-way, the v2 superblock is still valid (backup
  roots §11 of v2 are untouched).

### Step 2: Enable compression per dataset (online)

```
nvfs set compress=lz4 --dataset=<name>
```

- Sets `compress_default` in the dataset's ROOT_ITEM (stored in the root tree).
- New extents written after this point are compressed.
- Existing extents are **not** recompressed retroactively. To recompress: run
  `nvfs recompress --dataset=<name>` (offline background job; reads each extent,
  recompresses, replaces via CoW).

### Step 3: Enable dedup per dataset (online)

```
nvfs set dedup=on --dataset=<name>
```

- Sets `dedup_enabled` in the dataset's ROOT_ITEM.
- New extents are deduplicated inline.
- Existing extents are **not** retroactively deduplicated. To back-fill: run the v2
  offline dedup daemon (`duperemove`-equivalent, v2 §8) on existing extents first,
  then enable inline dedup for new writes.

### Step 4: Enable encryption per dataset (online, requires N7c)

Encryption interacts with the DHK (§V3-4.2). Enabling encryption after dedup has
already populated the DDT requires a DDT re-key: the existing Blake3 DDT keys must be
replaced with HMAC-DHK keys. This is done by `nvfs rekey --dedup-rehash --dataset=<name>`
(offline; reads each DDT entry, recomputes HMAC-DHK, rewrites the dedup B-tree entry).

**Recommended order:** enable encryption first (before dedup), so the DHK is derived
from the master key from the beginning and no re-hash is needed.

### Migration compatibility matrix

| v2 volume feature | v3 read | v3 write (no upgrade) | v3 write (after upgrade) |
|---|---|---|---|
| Uncompressed extents | OK | Same as v2 | OK; new extents compressed if opt-in |
| Offline dedup (reflinks) | OK | OK | OK; inline dedup adds to reflink pool |
| Encryption (N7c) | OK | OK | OK; DHK added if dedup also enabled |
| Blake3 checksums | OK | OK | OK; no change |

---

## V3-8. Updated open questions

In addition to v2 OQ-1 through OQ-8, v3 adds:

- **OQ-9:** DDT GC epoch — should refcount decrement be synchronous (in the write
  transaction) or deferred (background epoch GC like ZFS)? Synchronous is simpler but
  adds latency to unlink/truncate paths. Deferred risks leaked DDT entries on crash.
  Recommendation: synchronous for correctness in v3; switch to epoch GC as a follow-up
  if unlink latency becomes a bottleneck.

- **OQ-10:** Cross-dataset dedup — the per-dataset DHK (§V3-4.2) prevents cross-dataset
  dedup. For MODEL_IMMUTABLE datasets shared by multiple users (e.g., shared weight
  tensor pool), a shared DHK (per-pool) would enable cross-dataset dedup. This is a
  larger key-management change; deferred.

- **OQ-11:** Compressed ARC — should the ARC store compressed or decompressed blocks?
  v3 §V3-2.5 chooses decompressed (lower CPU, higher RAM). An `arc_compress=on` mount
  option could compress ARC entries for memory-constrained deployments. Deferred.

- **OQ-12:** Dedup ratio telemetry — `nvfs stats --dedup` should report DDT hit rate,
  space savings, and cold DDT miss rate so operators can decide whether to expand the
  hot DDT cache. The telemetry API is not yet specified; deferred to N7b implementation.

---

## V3-9. Updated capability table

| Capability | ...N6 | N7a | N7b | N7c | N8 |
|---|---|---|---|---|---|
| `COW` | Y | Y | Y | Y | Y |
| `Checksum` | Y | Y | Y | Y | Y |
| `Snapshot` | Y | Y | Y | Y | Y |
| `Clone` | Y | Y | Y | Y | Y |
| `Reflink` | Y | Y | Y | Y | Y |
| `SelfHeal` | Y | Y | Y | Y | Y |
| `SendReceive` | Y | Y | Y | Y | Y |
| `Dedup` | Y (offline) | Y (offline) | Y (inline) | Y (inline) | Y |
| `Encrypt` | - | - | - | Y | Y |
| `Scrub` | Y | Y | Y | Y | Y |
| `Compress` | - | Y | Y | Y | Y |
| `PosixCompat` | Y | Y | Y | Y | Y |
| `Quota` | - | - | - | - | future |
