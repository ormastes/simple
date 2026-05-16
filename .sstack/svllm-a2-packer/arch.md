# svllm A2-Packer — Phase 3 Architecture

**Author:** architect (Claude-solo, 2026-04-18)
**Scope:** data-flow + module split + binary/manifest layout + atomic-publish protocol
**Upstream context:** `state.md` §2-research, `audit.md` §§2/4/7/8

This file is design only — no .spl code blocks beyond signatures. Implementation is Phase 5.

---

## 1. End-to-end packer pipeline

```
argv
  │
  ▼
[svllm_pack/main.spl]         parse argv, dispatch subcommand
  │   convert <in.safetensors> <out_pack_root>
  ▼
[safetensors.spl]             read_all(in) → [u8]
  │                            parse_safetensors_header(bytes)
  │                              → (SafetensorsHeader, payload_offset)
  ▼
[tensor_pack.spl :: plan]     plan_pack(header, payload_len, caps)
  │                              → TensorPack { chunks[], tensors[] }
  │                            (groups tensors into ≤ DEFAULT_PREFERRED_CHUNK_BYTES
  │                             chunks aligned to DEFAULT_CHUNK_ALIGN)
  ▼
[tensor_pack.spl :: emit]     for each chunk:
  │                              slice = payload[chunk.span]
  │                              digest = sha256(slice)          (via std.common.crypto)
  │                              nvfs_client.create(tmp_path, Sealed)
  │                              nvfs_client.write(handle, slice)
  │                              nvfs_client.seal(handle)        (close + hash recorded)
  ▼
[manifest.spl :: serialize]   emit_manifest_sdn(pack)
  │                              → text (deterministic, sorted)
  │                            nvfs_client.create(manifest_tmp, AppendOnly)
  │                            nvfs_client.write(handle, text_bytes)
  │                            nvfs_client.seal(handle)
  ▼
[nvfs_client :: publish]      publish_atomic(pack_root, staged_files):
  │                             1. rename data-NNN.bin.tmp → data-NNN.bin   (N-many)
  │                             2. rename manifest.sdn.tmp  → manifest.sdn  (last)
  ▼
exit 0 (or 1 on any Err)
```

**Pipeline invariants:**
- Payload bytes are copied **exactly once** from safetensors input to chunk output (no intermediate rebuffering).
- Digest is computed on the source slice before the write; re-read for verification is deferred to `svllm_pack verify` (AC-7 follow-up).
- Manifest is serialized **after** every chunk has been sealed and its true `byte_len` + `digest_hex` known.

---

## 2. Module responsibility split

| Function | File | Rationale |
|---|---|---|
| argv parsing, subcommand dispatch, exit-code mapping | `src/app/svllm_pack/main.spl` | App layer; no lib dep on argv shapes |
| `read_safetensors_file(path) -> Result<(SafetensorsHeader, [u8]), SafetensorsError>` | `.../model_loader/safetensors.spl` | Adds real little-endian u64 decode + JSON parse over existing `parse_safetensors_header` stub |
| `parse_header_json(json_text) -> Result<SafetensorsHeader, SafetensorsError>` | same | Uses `std.common.json` if it works from `@gc`; else hand-rolled (flat schema only) |
| `plan_pack(header, payload_len, preferred_chunk_bytes, align) -> TensorPack` | `.../model_loader/tensor_pack.spl` | Pure planning; no I/O |
| `emit_chunks(pack, payload, client) -> Result<[ChunkDigest], PackError>` | same | I/O via `NvfsClient` trait — adapter decides std.fs vs. native nvfs |
| `sha256_of_slice(bytes, offset, len) -> text` | same (helper) | Thin wrapper over `std.common.crypto` |
| `emit_manifest_sdn(pack) -> text` | `.../model_loader/manifest.spl` | Deterministic SDN serializer; mirrors (future) parser's schema |
| `NvfsClient.publish_atomic(root, plan) -> Result<(), NvfsError>` | `.../nvfs_client/__init__.spl` | Trait method (added in A2 if missing) — delegates to adapter |
| `StdFsNvfsClient` (concrete adapter) | `.../nvfs_client/std_fs.spl` **(new)** | Wraps `rt_file_open/write_bytes/close/move`; returns `NvfsError.Unsupported` for pin/async/seal-with-extent-pinning |

**No module grows outside its family:** `tensor_pack.spl` never imports `std.fs`; all I/O funnels through `NvfsClient`. This keeps the A2 code portable to the future canonical nvfs adapter without rewrite.

---

## 3. Binary layout of `pack.bin` family

A2 ships **multi-file** layout (one `data-NNN.bin` per chunk), matching the A1 stub comment — **not** a single concatenated `pack.bin`. Rationale:

- Matches audit §2.2 / manifest schema (`chunks[].relative_path`).
- Each chunk becomes an independently sealable append-only object (R1). Single `pack.bin` would force whole-file seal and defeat chunk-level pin.
- Renaming N chunk files + 1 manifest is atomic per-file on POSIX `rename()`; the seal-then-publish ordering (§5) handles the cross-file visibility gap.

**Per-chunk file (`data-NNN.bin`)** — no framing header. The file *is* the raw aligned tensor bytes, nothing else. Framing lives in the manifest.

**Alignment constant (decided):** `DEFAULT_CHUNK_ALIGN = 4096` bytes.
- 4 KiB matches common NVMe LBA + typical `preferred_read_granule` floor.
- 64 KiB was considered but wastes up to 63 KiB per tensor for small tensors in the fixture (2×2 F32 = 16 B); 4 KiB gives ≤4 KiB worst-case tail per chunk.
- Manifest records actual tensor byte offsets within each chunk; padding is `0x00` and not hashed separately (sha256 covers padded chunk).

**Chunk-packing rule:** greedy — append tensors in header declaration order; start a new chunk when the next tensor would push chunk bytes past `DEFAULT_PREFERRED_CHUNK_BYTES` (2 MiB). Each tensor's `offset_in_chunk` is aligned up to `DEFAULT_CHUNK_ALIGN`.

**Decided constant location:** both constants exported from `tensor_pack.spl` as top-level `pub const`. (Answers audit §8 Q3.)

---

## 4. Manifest schema (v0, SDN)

Extends A1's stub struct. Emitted by `emit_manifest_sdn`; future parser (A3) must round-trip.

```
{
  schema_version: 0,
  model_id: text,                        # from safetensors __metadata__ or argv default
  revision: text,                        # "" if unknown
  preferred_chunk_bytes: i64,            # DEFAULT_PREFERRED_CHUNK_BYTES actually used
  chunk_align: i64,                      # DEFAULT_CHUNK_ALIGN
  digest_algo: text,                     # "sha256" (decided; see §6)
  chunks: [
    { id: i32, relative_path: text, byte_len: i64, digest_hex: text }
  ],
  tensors: [
    { name: text, dtype: text, shape: [i64],
      chunk_id: i32, offset_in_chunk: i64, byte_len: i64 }
  ]
}
```

- `tensors[]` ordered by header declaration order; `chunks[]` ordered by `id` ascending.
- All integers decimal, no leading zeros; `digest_hex` lowercase 64-char.
- `__metadata__` from safetensors is **dropped** in v0 (except `model_id` if present).

---

## 5. Atomic-publish protocol

**Staging:** `<out_pack_root>/` contains the partially-written artifacts with `.tmp` suffix:
```
data-000.bin.tmp
data-001.bin.tmp
…
manifest.sdn.tmp
```

**Required ordering (data before manifest):**

1. Write every `data-NNN.bin.tmp` fully.
2. `fsync` each `data-NNN.bin.tmp`. *(GAP: primitive missing — filed as FS-REQ-001.)*
3. Rename `data-NNN.bin.tmp` → `data-NNN.bin` for every N. Order within this step does not matter — the manifest is still invisible.
4. Write `manifest.sdn.tmp` fully.
5. `fsync` `manifest.sdn.tmp`. *(GAP: primitive missing — FS-REQ-001.)*
6. Rename `manifest.sdn.tmp` → `manifest.sdn`. **This is the publish fencepost.**
7. `fsync` the directory inode. *(GAP: primitive missing — FS-REQ-001.)*

**Visibility rule:** A reader opens `manifest.sdn` first. If it doesn't exist, the pack is considered absent (partial publish never observed). If it exists, the manifest's `chunks[].relative_path` **must** resolve — any missing data file is a bug, not a race.

**FAT32 failure mode (documented, filed as FS-REQ-002):**
- FAT32 `rename` is not atomic across FAT updates; a power-cut between steps 3 and 6 can leave some `data-NNN.bin` present but `manifest.sdn` absent → reader correctly treats as absent → **safe stale state** (must clean up `.tmp` + orphan chunks on next start).
- Mid-rename within a single chunk (step 3) can leave an empty directory entry on crash. Cleanup: on packer start, delete every `*.bin.tmp` and every `*.bin` without a corresponding manifest entry.
- No `fsync` = the kernel may reorder the rename vs. the data write on crash. Documented as acceptable for the bring-up adapter; real guarantee comes from nvfs R3 + R4.

**Recovery sketch (Phase 5 will implement in `svllm_pack verify` / cleanup path):** on retry, delete `*.tmp`; if `manifest.sdn` present, trust it; else delete matching `*.bin` siblings.

---

## 6. Open-question resolutions

| # | Question (audit §8) | Decision |
|---|---|---|
| 1 | `std.common.json` usable from `@gc`? | Try it first in Phase 5; fall back to a 150-line hand-rolled parser restricted to the flat safetensors schema. Parser lives in `safetensors.spl` (private fn) not `std.common` — avoids leaking a limited parser into common. |
| 2 | Digest algorithm | **sha256.** Verified present as `std.common.crypto.sha256`. BLAKE3 deferred (not in std today; A6 follow-up). Manifest records `digest_algo: "sha256"` so future packs can migrate. |
| 3 | Chunk-size / align constants | `pub const DEFAULT_PREFERRED_CHUNK_BYTES: i64 = 2 * 1024 * 1024` and `pub const DEFAULT_CHUNK_ALIGN: i64 = 4096` in `tensor_pack.spl`. |
| 4 | Adapter location | **Coupled** at `src/lib/gc_async_mut/svllm/nvfs_client/std_fs.spl`. Lift to `src/lib/nogc_sync_mut/fs/nvfs_std/` in A3 refactor once a second consumer exists. |

---

## 7. Error taxonomy (exit-code 1 triggers)

`svllm_pack` exits 0 only on full success. Every other path exits 1 with a one-line diag to stderr. Error classes:

| Class | Origin | Message prefix |
|---|---|---|
| `SafetensorsError.ShortPrefix` | header < 8 bytes | `svllm-pack: malformed input: ` |
| `SafetensorsError.BadLength` | N > file size | same |
| `SafetensorsError.MalformedJson` | JSON parse fail | same |
| `SafetensorsError.UnsupportedDtype` | dtype not in weight_utils table | `svllm-pack: unsupported dtype: ` |
| `SafetensorsError.OffsetOutOfRange` | `data_offsets` inconsistent | `svllm-pack: malformed input: ` |
| `PackError.PlanEmpty` | zero tensors in header | `svllm-pack: empty pack` |
| `NvfsError.Io` | any `rt_file_*` returns < 0 | `svllm-pack: io error: ` |
| `NvfsError.Unsupported` | adapter refuses (seal, pin) | `svllm-pack: adapter unsupported: ` |
| `ManifestError.Serialize` | sdn emit fail (should not happen) | `svllm-pack: manifest serialize error` |

Exit 0 also requires: every planned chunk wrote its expected `byte_len` back; digest matched the in-memory sha256; rename of every file succeeded.

---

## 8. Dependency map (no cycles)

```
svllm_pack/main.spl
  ├── safetensors.spl                    (parse)
  ├── tensor_pack.spl                    (plan + emit)
  │     └── nvfs_client (trait)
  │           └── nvfs_client/std_fs.spl (adapter) → rt_file_*
  └── manifest.spl                       (serialize)
        └── tensor_pack.spl              (TensorPack type only)
```

`safetensors.spl` and `manifest.spl` are siblings; neither imports the other. `tensor_pack.spl` imports `nvfs_client` only through the trait, keeping the planner pure.

---

## 9. Boundaries honored

- **No edits to** `doc/05_design/nvfs_design.md` (parallel track owns it).
- **No edits to** `src/lib/nogc_sync_mut/fs/nvfs/` (parallel track scaffolding).
- All append-only edits restricted to `doc/05_design/nvfs/svllm_requirements.md` (see `requirements_append.md` sibling — actually appended directly per AC-6).
- New files confined to disjoint scope declared in state.md §1-dev coordination notes.

**End of arch.md.**
