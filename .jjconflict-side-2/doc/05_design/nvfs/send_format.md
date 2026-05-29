# NVFS Send Stream Format (NVSR)

**Milestone:** N6b — raw send / encrypted replication stream
**Status:** Implemented (`examples/nvfs/src/core/send.spl`)
**Related:** `nvfs_design_v2.md §14` (encryption); `nvfs_requests.md FR-NVFS-N6b-001`

## Purpose

The NVFS raw send stream (`NVSR`) transports a sealed arena between peers
without requiring the receiver to decrypt.  Ciphertext travels verbatim;
only a holder of the dataset key can mount the received arena.  Unencrypted
arenas are also supported (flag bit 0 clear).

## Stream Layout

### Leading 16-byte header

| Offset | Size | Field | Notes |
|--------|------|-------|-------|
| 0 | 4 | `magic` | ASCII `NVSR` (0x4E, 0x56, 0x53, 0x52) |
| 4 | 2 | `version` | u16 LE; currently 1 |
| 6 | 2 | `flags` | u16 LE; bit 0 = encrypted; bit 1 = reflink-compressed (N6c) |
| 8 | 4 | `arena_count` | u32 LE; number of arenas in this stream |
| 12 | 1 | `checksum_algo` | 0=none (N6b); 1=CRC32C; 2=SHA-256 |
| 13 | 3 | `reserved` | must be zero |

### Per-arena records

Records follow the header in order until all arenas are exhausted.

#### Arena-begin record (type=0)

| Size | Field |
|------|-------|
| 1 | `record_type` = 0 |
| 8 | `arena_id` (u64 LE; sender-side arena id) |

#### Extent record (type=1)

| Size | Field | Condition |
|------|-------|-----------|
| 1 | `record_type` = 1 | |
| 8 | `arena_id` (u64 LE) | |
| 8 | `logical_off` (u64 LE) | byte offset within arena |
| 8 | `phys_ptr` (u64 LE) | stub = logical_off for N6b |
| 4 | `len` (u32 LE) | payload byte count |
| 4 | `birth_gen` (u32 LE) | generation at which extent was written |
| 32 | `checksum` | algo-specific; zeros when `checksum_algo=0` |
| 12 | `encrypted_nonce` | only present when `flags & 1` (encrypted bit set) |
| len | payload | ciphertext (AES-GCM ct || 16-byte tag) or plaintext |

#### Arena-end record (type=2)

| Size | Field |
|------|-------|
| 1 | `record_type` = 2 |
| 8 | `arena_id` (u64 LE) |

## Encryption semantics

When `flags bit 0` is set:

- Sender calls `encrypt_arena_data(ks, key, arena_id, logical_off, plaintext)`.
- The 12-byte deterministic IV (from `_make_iv(arena_id, offset)`) is stored in
  `encrypted_nonce`.
- `payload = ciphertext || 16-byte GCM tag`.
- Receiver with correct key: calls `decrypt_arena_data`; `Err(Corrupt)` on tag
  mismatch (wrong key or tampered ciphertext).
- Receiver with no key: stores payload verbatim; sets `encrypted_opaque=true`
  in `ReceiveResult`.  Arena cannot be mounted until key is presented.

## Checksum algorithms

| Code | Algorithm | Status |
|------|-----------|--------|
| 0 | None | N6b (zeros stored) |
| 1 | CRC32C | Planned FR-NVFS-N6b-002 |
| 2 | SHA-256 | Planned FR-NVFS-N6b-003 |

## Cross-implementation compatibility

The magic `NVSR` and version field allow future implementations (SimpleOS
in-kernel replication, external backup tools) to detect and skip unknown record
types gracefully.  Unknown record types must be treated as corrupt by N6b
receivers.
