# svllm Filesystem Requirements for nvfs

- **Audience:** the parallel nvfs (NVMe-aware filesystem) design agent/track
- **Author:** svllm track
- **Status:** v0 — initial upfront contribution, derived from the svllm master plan (`../svllm/svllm_master_plan.md`) and the attached research doc
- **Last-updated:** 2026-04-18
- **Companion docs:** `./README.md` (index for this directory), `../svllm/fs_requests/` (secondary reactive feature-requests captured during implementation)

## Why this doc exists

svllm is being built in parallel with nvfs. The goal of this file is to state — **upfront, before svllm hits FAT32 walls** — exactly what filesystem API and semantics the serving engine needs, so nvfs design choices are made with a real client in mind. The existing FAT32 stack is only a bring-up substrate; svllm's real performance target is on nvfs.

This doc does **not** specify how nvfs should be implemented (that is nvfs's job). It specifies what svllm will call, with what expected behavior and rough perf envelope, and which requirements are load-bearing vs. nice-to-have.

## Workload profile (what svllm actually does to storage)

| Traffic class | Size | Read/write | Latency sensitivity | Hot path |
|---|---|---|---|---|
| Tensor-pack chunk read | 1–16 MiB aligned ranges | Read only, sequential-within-chunk | Medium (TTFT) | Yes |
| Tensor-pack manifest | 4–256 KiB | Read once, read-mostly | High at load time | Yes |
| Safetensors ingest (packer tool) | Entire upstream checkpoint, streaming | Read | Low | No |
| Packed model publish | New tensor pack + manifest | Append, then atomic rename/flip | Low–medium | No |
| Adapter (LoRA) chunk read | 4 KiB–64 MiB | Read only, many small files | Medium | Yes (hot-swap) |
| KV prefix-cache spill (optional, off-hot-path) | 64 KiB–4 MiB per prefix | Read/write, append-plus-GC | Low (best-effort) | No |
| Telemetry / logs | 4 KiB records | Append only | Low | No |
| Config, tokenizer, sampling params | < 1 MiB | Read only | Medium at load | Yes |

"Hot path" means the request-per-token decode loop or the model-switch critical path.

## Object class taxonomy svllm will request

svllm will create objects via `fs_create(class, flags)` with these class values (terms from research doc "Exported APIs" table):

| Class | Semantics svllm requires | Example object |
|---|---|---|
| `tensor_pack` | Sealed after write, pinned extents (cleaner must not relocate), large aligned reads, no overwrite | `/models/llama3-8b/weights.pack` |
| `manifest` | Small, read-mostly, atomically publishable via rename/flip; older version must remain readable until new one is committed | `/models/llama3-8b/manifest.json` |
| `adapter` | Many small sealed objects in one directory; fast directory listing required | `/adapters/{user}/{name}.lora` |
| `append_only` | Log-style append; read back for resume | `/svllm/telemetry/2026-04-18.log` |
| `temp` | Short-lived, best-effort durability, preferred for scratch/sort spill | `/svllm/tmp/<request-id>` |
| `kv_spill` (optional) | Large, append-only segments with explicit `fs_trim` at eviction time; reads from multiple concurrent request handlers | `/svllm/kv/prefix-<hash>.blob` |
| `mutable` | Small configs and runtime state that can be overwritten; fallback class only | `/svllm/state.json` |

If nvfs uses a different class taxonomy, the mapping must preserve: immutability (for `tensor_pack`, `manifest`, `adapter`), pinning (for `tensor_pack`), atomic publish (for `manifest`), and explicit trim (for `kv_spill`).

## Required API surface

svllm's loader and engine will call the following. **All calls must be safe from async-runtime contexts** (svllm lives in `gc_async_mut`; the async HTTP bridge and monoio reactor must not be blocked by any of these).

### R1. Object lifecycle (load-bearing, P0)

- `fs_create(class, flags) -> ObjHandle` — class as above; flags include `{create_new, truncate_existing, initial_size_hint}`.
- `fs_open(path, mode) -> ObjHandle` — read-mostly modes must not pay write-path costs.
- `fs_seal(obj, pin_extents=true) -> ()` — after seal, writes fail; if `pin_extents=true`, the cleaner must not relocate any extent of this object until `fs_trim(obj)` is called. This is **the** requirement that makes `tensor_pack` manifests' offsets stable across runtime.
- `fs_trim(obj)` / `fs_trim(obj, ranges)` — explicit deallocate / TRIM. svllm calls this at model uninstall and at KV-spill eviction. Must not block.
- `fs_close(obj) -> ()` — releases handle only; does not imply durability.

### R2. Aligned async reads into pinned buffers (load-bearing, P0)

- `fs_read_range(obj, off, len, buf) -> Future<()>` where `buf` is a registered pinned DMA buffer handle (see R6).
- Must honor a **preferred read granule** returned by `fs_query_caps` (§R5). svllm will align all tensor-pack reads to that granule.
- Must support **at least 64 concurrent outstanding reads per handle** without head-of-line blocking.
- Target throughput on one conventional NVMe namespace: **≥ 80% of the device's advertised seq-read bandwidth** for 2 MiB chunks when buffers are pre-registered.

### R3. Atomic manifest publish (load-bearing, P0)

Either of these must be provided (svllm does not care which, but exactly one must be atomic w.r.t. crash and w.r.t. concurrent readers):

1. `fs_replace(obj, logical_off=0, iov, expected_gen) -> NewGen` followed by `fs_sync(scope=root_durable, epoch)` — old content remains readable to any handle opened before the replace completes.
2. `fs_publish(temp_obj, final_path) -> ()` — rename + fsync equivalent; atomic w.r.t. readers and crash.

svllm will publish new model versions by (a) writing tensor_pack chunks, (b) sealing them, (c) writing a temp manifest, (d) calling the atomic publish. If neither pattern is supported, svllm has to stop the serving engine to swap models — which defeats the `sleep(level=0)` / warm-switch design.

### R4. Durability scopes (load-bearing, P0)

svllm needs three distinguishable durability levels, per the research doc's "durability scopes":

- `fs_sync(obj_or_scope, scope=submitted)` — host has handed bytes to the device; no guarantee.
- `fs_sync(obj_or_scope, scope=media_durable, epoch)` — bytes are on nonvolatile media (NVMe Flush or FUA semantics).
- `fs_sync(scope=root_durable, epoch)` — media-durable AND the filesystem root/checkpoint publication is also durable. svllm uses this only when an atomic manifest publish must survive a crash.

svllm commits **never** call the middle or high scopes on the hot decode path. They are only used at publish boundaries.

### R5. Capability query (load-bearing, P0)

`fs_query_caps(obj_or_path) -> Caps` returning at least:

- `lba_size`, `preferred_read_granule`, `preferred_write_granule`
- `max_concurrent_ops_per_handle`
- `atomic_write_unit`, `atomic_boundary`
- `supports_sealed_pin`, `supports_atomic_publish`, `supports_trim`
- `zone_size` / `append_granule` when backing is ZNS (NULL when conventional)
- `write_cache_volatile: bool`

svllm will downgrade gracefully (e.g., fall back to copy-based model switch if `supports_atomic_publish=false`) but will emit a structured warning and record a Phase-B1 feature-request.

### R6. Pinned DMA buffer registration (load-bearing, P0)

- `fs_register_buffer(buf_ptr, len) -> BufHandle` — once registered, the same buffer is reused for all tensor-pack streaming reads; nvfs/the NVMe layer keeps the IOVA translation cached.
- `fs_unregister_buffer(BufHandle)` — called at svllm shutdown / model unload.
- Interop with `src/lib/gc_async_mut/gpu/pinned_pool.spl` (new): svllm's pinned pool allocates via OS + `cuMemHostRegister`-equivalent, then registers with nvfs. nvfs must tolerate buffers that are already pinned for GPU transfer (double-registration is legal).

### R7. Advise hints (nice-to-have, P1)

`fs_advise(obj, lifetime, qos, residency)` where:

- `lifetime ∈ {short, warm, cold, immutable}`
- `qos ∈ {WAL, foreground_read, model_prefetch, background}`
- `residency ∈ {any, prefer_resident, prefer_evict}`

svllm will tag tensor-pack reads as `(immutable, model_prefetch, prefer_resident)` and KV spill as `(short, background, prefer_evict)`. If nvfs ignores hints entirely, svllm still works; if it honors them, model cold-start under mixed load should improve.

### R8. Async listing (nice-to-have, P1)

`fs_list(dir) -> Iter<ObjMeta>` that completes in sublinear time for directories with 1–10k adapter files. Used for adapter discovery at boot.

### R9. Checksums (nice-to-have, P1, optional)

If nvfs computes per-extent or per-chunk checksums and exposes them, svllm will skip its own checksum on the hot path. If nvfs doesn't, svllm computes its own over the manifest's checksum tree.

## Non-requirements (explicit)

- svllm does **not** need POSIX semantics (no mmap, no seek, no hierarchical permissions beyond owner/class).
- svllm does **not** need write-back page cache (its pinned-pool staging is the cache). A filesystem page cache that duplicates this would hurt, not help.
- svllm does **not** depend on fsync-at-every-write. Models publish in large epochs.
- svllm does **not** depend on zoned namespaces or FDP. Both are accelerators nvfs can adopt later; svllm must work on conventional NVMe (`supports_sealed_pin=true` emulated in software is fine).

## Perf budget (approximate, to be refined by measurement)

| Operation | Target on mid-range NVMe (7 GB/s seq, 300k IOPS) |
|---|---|
| Cold load 8B-param model (≈16 GB fp16) from sealed tensor_pack | ≤ 4 s end-to-end (first token capable in < 2 s with overlapped H2D) |
| Manifest atomic publish | ≤ 50 ms |
| Adapter hot-swap (64 MiB LoRA) | ≤ 50 ms |
| 2 MiB tensor read, pinned buf, warm cache | ≤ 300 µs p99 |
| `fs_trim` on a 10 GiB tensor_pack | ≤ 200 ms, can be async |

These are targets, not acceptance gates — they are here so nvfs can evaluate design tradeoffs.

## Interaction with runtime families

- svllm's callers are in `src/lib/gc_async_mut/svllm/…` (GC + async + mut).
- The nvfs client shim svllm uses should live in `src/lib/gc_async_mut/nvfs_client/` and adapt to whatever the canonical nvfs API is. Keeping it in `gc_async_mut` means svllm can use GC-managed handles and awaitable futures. If nvfs's native API is `nogc_async_mut` or `nogc_async_mut_noalloc`, the client shim bridges.
- Per the existing semantic-lint runtime-family check (`src/compiler/35.semantics/gc_boundary_check.spl`), the shim's internals must stay allocation-free in hot paths.

## Alignment with research doc & master plan

| Source section | This doc's section |
|---|---|
| Research doc "Exported APIs" table | R1, R2, R3, R4, R7 |
| Research doc "Crash consistency and recovery" | R3, R4 |
| Research doc "Block mapping and immutable-extent semantics" | R1 (`sealed` + `pin_extents`) |
| Master-plan A1/A2 (tensor-pack + packer) | R1, R2, R3, R5 |
| Master-plan A3 (streaming loader + pinned staging) | R2, R6 |
| Master-plan A4 (paged KV cache) | R1 (`kv_spill`), R7 |
| Master-plan A7 (sleep/wake) | R3 (atomic manifest swap) |
| Master-plan A8 (LoRA adapter) | R1 (`adapter` class), R8 |

## Open coordination questions for the nvfs agent

1. Will nvfs expose `sealed + pin_extents` semantics on conventional NVMe from day one, or only on ZNS? svllm's A1 loader needs it on conventional.
2. What is the buffer-registration model (shared with an io_uring-like ring, or a separate API)? This affects how svllm wires its pinned pool.
3. Is `fs_publish` supported or do we use `fs_replace` + `fs_sync(root_durable)`?
4. What's the expected `preferred_read_granule` range? svllm currently plans 2 MiB tensor chunks.
5. Will nvfs ship a user-space library binding svllm links against, or a syscall ABI through a capability handle?

Please reply in this file (inline) or by creating `./nvfs_design.md` and linking responses there; svllm will update R1–R9 based on the answers.

---

## R1 Append-Only Object Class — Concrete Spec

- **Status:** appended 2026-04-18 by svllm A2-packer Phase 3 architect. Scope: make R1's `append_only` class precise enough that the svllm packer and the future nvfs adapter can implement/verify it without further clarification.
- **Companion spec:** R3 below (publish ordering) assumes these semantics.

### Object state machine

```
[OPEN] ── append(bytes) ──▶ [OPEN]        (size grows monotonically)
   │
   │ seal()
   ▼
[SEALED] ── any mutation ──▶ ERROR.Sealed (reject, no-op)
   │
   │ delete()   (requires cap + !pin_extents)
   ▼
[GONE]
```

- Only two externally visible states (`OPEN`, `SEALED`). `GONE` is the tombstone after delete.
- An object is created in `OPEN` state via `fs_create(path, class=append_only, flags)`. Creation is idempotent only when `flags.create_new = false`; by default, creating over an existing path errors.

### Allowed operations per state

| Op | OPEN | SEALED | Notes |
|---|---|---|---|
| `append(handle, bytes)` | ✅ | ❌ `Sealed` | Bytes append at current size; partial writes allowed but each call is atomic w.r.t. size. |
| `truncate(handle, n)` | ❌ `InvalidOp` | ❌ `Sealed` | Append-only: truncate never legal, even while open. |
| `write_at(handle, off, bytes)` | ❌ `InvalidOp` | ❌ `Sealed` | Random writes never legal. |
| `read_at(handle, off, len)` | ✅ | ✅ | Readable in both states (live readers see partial OPEN content). |
| `seal(handle)` | ✅ → SEALED | no-op (idempotent) | See size/hash rules below. |
| `stat(handle)` | ✅ | ✅ | `size` + `state` always queryable. |
| `delete(path)` | ✅ (best effort) | ✅ (if no `pin_extents`) | SEALED + pinned → `Pinned` error. |
| `rename(src, dst)` | ✅ | ✅ | State preserved across rename. |

### Size-at-seal

- At `seal()`, the object's byte length is **frozen**. The returned `SealReceipt` contains the final `size: i64`; subsequent `stat()` must return this exact value forever.
- The adapter MUST reject any buffered-but-not-yet-flushed append that would race the seal. Semantics: `seal()` is a fence — all prior successful `append` calls are included, no later `append` is accepted.
- A zero-length seal is legal (empty sealed object). Consumers SHOULD still validate digest coverage.

### Hash-at-seal

- If the object was created with `flags.hash_on_seal = true` (default for tensor-pack chunks and manifests), `seal()` returns `digest_hex: text` computed over the entire final content.
- Algorithm: **sha256** for manifest v0 (see arch.md §6 open-question resolution 2). Adapter MAY also compute BLAKE3; in that case the receipt returns both — client picks the one matching its manifest's `digest_algo`.
- If `hash_on_seal = false`, `digest_hex` is `""` and the client is responsible for out-of-band verification.
- Digest is computed **once** during seal from the adapter's internal write path (ideally as bytes flow to storage); re-reading post-seal to re-digest is wasteful and MUST NOT be required to prove integrity.

### Rejection rules post-seal

- Any call that would mutate the content (`append`, `write_at`, `truncate`, changing class flags) returns `NvfsError.Sealed` deterministically — never `InvalidOp`, never silent no-op.
- `fs_sync(durable)` on a SEALED object is a no-op success: the object is already final.
- Attempting to re-seal returns success (idempotent) — but the returned receipt MUST match the original (same size, same digest_hex). Adapters MUST cache the seal receipt.

### GC / delete semantics

- `delete(path)` on an OPEN object is legal and implicitly seals-then-deletes; any live readers keep their handle valid until close (POSIX-style unlink-while-open).
- `delete(path)` on a SEALED object with `pin_extents = true` returns `NvfsError.Pinned`. Client must first call `unpin(handle)` with a cap. This prevents accidental GC of hot tensor-pack chunks.
- `delete(path)` on a SEALED object without pinning frees storage immediately on conventional NVMe; on ZNS, reclaim is deferred to zone reset.
- Tombstones (`GONE`) are not observable by clients; `fs_create` on a GONE path is equivalent to creating from scratch.

### Failure surface

- `Sealed` — mutation after seal.
- `InvalidOp` — op illegal regardless of state (truncate, write_at).
- `Pinned` — delete of a pinned sealed object.
- `SizeMismatch` — seal with explicit `expected_size` fails if actual ≠ expected (optional check, used by the packer).
- `Io`, `NoSpace`, `Unsupported` — inherited from the general adapter surface.

### Adapter conformance test (svllm-maintained)

The svllm track will ship a spec under `test/unit/lib/gc_async_mut/svllm/nvfs_client/` that exercises the full state machine against whatever `NvfsClient` implementation is provided. Nvfs implementations pass by making this spec green. FAT32 bring-up adapter is expected to fail `pin_extents` + `hash_on_seal` paths and MUST return `Unsupported` (not silently mis-behave).

---

## R3 Atomic Manifest Publish — Ordering Rules

- **Status:** appended 2026-04-18 by svllm A2-packer Phase 3 architect.
- **Relates to:** R3 above, which stated the requirement at the black-box level. This section fixes the **exact sequence** that svllm's packer will execute and that nvfs MUST preserve the visibility semantics of.

### Required ordering (data before manifest)

For a pack with N data chunks and 1 manifest, the publisher MUST execute the following steps in this exact order. An implementation that reorders steps 1–3 vs. 4–6 is non-conformant:

1. `fs_create(data-K.bin.tmp, append_only, hash_on_seal=true)` + stream appends + `seal()` — for every K in [0, N).
2. `fs_sync(data-K.bin.tmp, scope=data_durable)` — for every K.
3. `fs_rename(data-K.bin.tmp → data-K.bin)` — for every K. Order among K is free; none of these names are yet referenced by any live reader path.
4. `fs_create(manifest.sdn.tmp, append_only, hash_on_seal=true)` + stream append + `seal()`.
5. `fs_sync(manifest.sdn.tmp, scope=data_durable)`.
6. `fs_rename(manifest.sdn.tmp → manifest.sdn)` — **publish fencepost.** Before this step, no reader can observe any part of the new pack; after, the entire pack is visible.
7. `fs_sync(pack_root/, scope=metadata_durable)` — directory barrier. Ensures the rename is durable across a crash.

### Visibility atomicity guarantee

- **Reader protocol:** open `manifest.sdn` first. Absence = pack absent. Presence = every chunk listed in the manifest's `chunks[].relative_path` MUST be openable and have matching `byte_len` + `digest_hex`. Any discrepancy is a corruption bug, not a race.
- **Writer protocol:** the packer MUST NOT write `manifest.sdn` (final name) at any point before step 6. It MUST NOT partially update an existing `manifest.sdn` — the only legal write path is `.tmp` → seal → rename.
- Crash between any two steps leaves the old pack visible (or nothing, if initial publish) — never a mixed state. This is the load-bearing invariant for R3.

### fsync + directory-fsync requirements

- Steps 2 and 5 require **file fsync** (`fs_sync(handle, scope=data_durable)`). Without it, a post-rename crash can lose the file body while preserving the directory entry — reader sees a truncated chunk or manifest.
- Step 7 requires **directory fsync** (`fs_sync(dir_handle, scope=metadata_durable)`). Without it, a crash can revert the rename even though the file body is durable — reader sees the pre-rename state (old pack or no pack), which is itself safe but wastes a publish.
- **nvfs MUST provide both primitives.** The current runtime lacks them — tracked as `FS-REQ-001-fsync-primitive` under `doc/05_design/svllm/fs_requests/`.

### Rename fencepost rules

- The rename in step 6 MUST be atomic w.r.t. readers: at no observable instant is the destination name half-written, half-old, or absent (if a prior manifest existed).
- POSIX `rename(2)` within a single directory on ext4/xfs/btrfs satisfies this. FAT32 does **not** — it is a delete-then-create sequence with a visible gap. svllm's FAT32 bring-up accepts this gap and documents it as a known degraded-mode risk (`FS-REQ-002-fat32-rename-atomicity`).
- `rename` from one directory to another is **disallowed** for the publish fencepost; publisher MUST stage `.tmp` in the same directory as the final name.

### Recoverability after crash mid-publish

The packer (and any future `svllm_pack verify` / cleanup) MUST tolerate the following crash points and recover to a consistent state:

| Crash between steps | State seen at restart | Required cleanup |
|---|---|---|
| 1 ↔ 2 | `data-K.bin.tmp` may exist, possibly empty/partial | Delete all `*.tmp` in pack_root. |
| 2 ↔ 3 | Same as above; some files durable | Same cleanup. |
| 3 ↔ 4 | Some/all `data-K.bin` present; no manifest | Delete all `*.bin` without manifest entry (there is none). Retry from step 1 or abort. |
| 4 ↔ 5 | `manifest.sdn.tmp` exists; not yet durable | Delete it; keep data files; caller may retry step 4. |
| 5 ↔ 6 | `manifest.sdn.tmp` durable; final name absent | Delete `*.tmp`; treat pack as absent. (Safe: the rename never landed.) |
| 6 ↔ 7 | Final `manifest.sdn` present but dir not fsynced | On crash-recovery: the rename may or may not have survived the cache. If it did, pack is live. If not, pack is absent. Either is consistent. |
| after 7 | Published and durable | None. |

**Key invariant:** at no crash boundary can a reader observe `manifest.sdn` pointing to a chunk that does not exist or whose bytes don't match the recorded digest. The ordering rules above are necessary AND sufficient to guarantee this, given correct fsync + atomic rename from the underlying FS.

**End of R1/R3 append, 2026-04-18.**
