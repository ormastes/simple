# spostgre Filesystem Requirements for nvfs

- **Audience:** the parallel nvfs (NVMe-aware filesystem) design agent/track
- **Author:** spostgre track (SStack Phase 3, `.sstack/spostgre-nvfs-storage/`)
- **Status:** v0 — initial upfront contribution, derived from the spostgre research doc (`doc/01_research/spostgre_research.md`) and the spostgre engine design (`../spostgre_design.md`)
- **Last-updated:** 2026-04-18
- **Companion docs:**
  - `./README.md` — index for this directory
  - `./svllm_requirements.md` — parallel upfront contribution from the svllm track (load this first; this doc follows its schema)
  - `../svllm/svllm_master_plan.md` — svllm master plan (context only)
  - `../nvfs_design.md` — NVFS design that consumes both this file and `svllm_requirements.md`
  - `../spostgre_design.md` — spostgre engine design that originates these requirements

---

## Why this doc exists

Per the memory note `feedback_svllm_drives_nvfs_design.md`, **upfront design contributions are the primary channel** through which upstream consumers steer NVFS. The post-hoc feature-request backlog at `doc/08_tracking/feature_request/nvfs_requests.md` is the **secondary** channel, for discoveries made during Phase 5+ implementation.

This document is spostgre's upfront contribution. It sits alongside `svllm_requirements.md` (same directory), so the NVFS designer can reconcile both in one pass.

spostgre commits to this contract in `../spostgre_design.md §11` ("NVFS interface assumptions") — every storage API call listed there maps to one of the S-entries below, and the engine milestones M1–M5 each depend on a named subset of the S-entries.

---

## Companion to svllm_requirements.md

spostgre and svllm make partially overlapping demands on NVFS. Where they align, NVFS should serve a single primitive; where they diverge, NVFS must serve both without forcing either track to degrade.

### Alignment / divergence matrix

| Concern | spostgre need | svllm need | Action for NVFS |
|---|---|---|---|
| Sealed-after-write objects | `arena_seal` for checkpoints (durable, compactable, generation-pinned) | `fs_seal` on tensor_pack / adapter objects | **Unify:** one `arena_seal(arena) -> SealToken` primitive; spostgre uses seal + generation pinning, svllm uses seal + immutability |
| Atomic publish | pmap-root swap for checkpoint commit (8–16 B record) | manifest rename/flip (arbitrary-size JSON) | **Unify:** generic `atomic_pointer_record_publish(name, bytes, expected_gen) -> PublishResult`. spostgre's pmap CAS and svllm's manifest flip share this abstraction |
| Pinned buffers | Not required at M1 (sync path); useful at M3 (AIO) | **Required from v0** (weight streaming to GPU) | NVFS must offer `fs_register_buffer` from milestone N2; spostgre adopts it at its M3 |
| Append arenas | WAL aligned-append to device granule | `append_only` telemetry logs | **Unify:** `arena_append_aligned(arena, bytes, granule) -> Offset`. Both consumers converge on the same call; WAL needs group-commit semantics on top |
| Short-lived scratch | DB_TEMP for sort spill, hash build | `temp` for request-local scratch | **Unify:** `DB_TEMP` class; drop-on-mount semantics satisfy both |
| Durability classes | Fine-grained (per-WAL-record durability) | Coarse (per-object durability) | NVFS offers per-op durability flag; both use the same flag space |
| Clone-range | Page-version clone during checkpoint compaction | Not required | spostgre-only; NVFS offers `arena_clone_range` as a P1 primitive, spostgre pays for it |

### Convergence candidates (NVFS author: please reconcile)

- **C1.** `atomic_pointer_record_publish` subsumes both pmap-root CAS and manifest flip. Semantics: publish a small opaque record under a named slot; accept an `expected_generation` for CAS. The record's bytes are opaque to NVFS; it only needs durability + generation bump + old-gen reader-pinning.
- **C2.** `arena_seal` is a single primitive serving both checkpoint-commit (spostgre) and weight-seal (svllm). The distinction is purely in caller policy, not in NVFS.
- **C3.** `arena_append_aligned` unifies WAL and telemetry logs. spostgre needs a group-commit helper on top; svllm does not, but the underlying call is the same.

---

## Workload profile (what spostgre actually does to storage)

To help NVFS size its primitives correctly, here's spostgre's I/O profile:

| Dimension | Value / range | Notes |
|---|---|---|
| Page size | 8 KiB fixed | PostgreSQL-compatible |
| Atomic-write unit required | ≤ page size when device AWUPF ≥ 8 KiB; else intent-log fallback | Capability-probed |
| WAL record size | 64 B – 64 KiB | Most commits are 128 B – 4 KiB |
| WAL flush granule | device-preferred-write-granule (typically 4 KiB – 16 KiB); group-committed | Must be aligned append |
| Peak commit IOPS | 20 K – 200 K ops/s single-node | Dominates WAL arena hot path |
| Page-version churn | 10^4 – 10^6 new page-versions/s under heavy OLTP | Dominates main arena write path |
| Checkpoint arena size | 0.5 – 4 GiB per epoch | Sealed, compacted in background |
| pmap entry count | up to 128 M entries (1 TiB relation) | Two-level structure; see §OQ-4 of research |
| Blob (TOAST) object size | 4 KiB – 1 GiB | WiscKey-style; reads are seek+contiguous |
| Read working set | 5 % – 60 % of relation size, skewed | Hot pages pinned in buffer pool; cold pages served by NVFS |

spostgre expects to drive NVFS near the device's 4K-random-write durability envelope during sustained OLTP. Benchmark discipline requires NVFS to honor the SSD-iq critique (see research §8): NVFS must expose `fs_caps().write_amp_hint` so spostgre can report realistic WAF numbers without guessing.

---

## Required API surface

Numbering uses prefix **S** (for spostgre) to avoid collision with svllm's `R1..R9`.

### S1. arena_create per storage class (load-bearing, P0)

```
fn arena_create(class: StorageClass, hint: ArenaHint) -> Result<ArenaId, FsErr>
```

- **StorageClass** is the authoritative 6-class enum defined in `../nvfs_design.md §3`. spostgre uses: `META_DURABLE` (catalog), `DB_WAL` (wal fork), `DB_TEMP` (temp fork, hash build, sort spill), `GENERAL_MUTABLE` (rel.main, rel.pmap, rel.vmap, rel.fmap), `CHECKPOINT_SNAPSHOT` (sealed checkpoint arenas), `MODEL_IMMUTABLE` (unused by spostgre; svllm only).
- **ArenaHint** may carry: expected size, preferred granule, locality group (for FDP PID), ZNS-zone hint.
- **Failure modes:** out-of-space, invalid class for this mount, capability-probe mismatch.
- **Durability after create:** arena metadata durable; no data yet.

### S2. arena_append_aligned (load-bearing, P0)

```
fn arena_append_aligned(
    arena: ArenaId,
    bytes: Slice<u8>,
    granule: u32,
    durability: Durability
) -> Result<Offset, FsErr>
```

- Append `bytes` at an offset that is a multiple of `granule`. NVFS may pad. Returns the starting offset.
- `granule` is queried via `fs_caps().preferred_write_granule` at boot; it is not a guess.
- `Durability ∈ { BUFFERED, DURABLE_ON_RETURN, DURABLE_GROUP_COMMIT }`. spostgre WAL uses `DURABLE_GROUP_COMMIT`, which NVFS implements by coalescing concurrent appends until one NVMe Flush / FUA completes.
- **Group-commit helper:** `arena_group_commit(arena)` waits until the current in-flight group is durable; returns the highest offset known durable.
- **Failure modes:** media error → spostgre fails the WAL write and retries a new arena (crash-safe); out-of-space → spostgre seals current WAL arena and opens a new one.

### S3. arena_seal + arena_discard with generation pinning (load-bearing, P0)

```
fn arena_seal(arena: ArenaId) -> Result<SealToken, FsErr>
fn arena_discard(arena: ArenaId, keep_gen_above: Generation) -> Result<(), FsErr>
```

- `arena_seal` flips the arena to read-only, flushes metadata durably, and returns a `SealToken` carrying the seal's generation number.
- `arena_discard` frees the arena **only when every generation at or below `keep_gen_above` is drained**. NVFS tracks open readers per generation; it refuses the discard if any snapshot still pins an earlier generation.
- spostgre MVCC uses this exactly: a sealed checkpoint arena cannot be discarded until every transaction snapshot predating its seal has completed (research §11.3).
- **Failure modes:** `DiscardBlocked(held_generations)` → spostgre delays vacuum and retries.

### S4. arena_clone_range for page-version cloning (load-bearing, P0)

```
fn arena_clone_range(
    src: ArenaId, src_off: Offset,
    dst: ArenaId, dst_off: Offset,
    len: u64
) -> Result<(), FsErr>
```

- Copy `len` bytes from `(src, src_off)` to `(dst, dst_off)`. On capable devices, NVFS implements via NVMe `Copy` or ZNS `Zone Append`; on baseline NVMe, it falls back to read-then-write in NVFS (no bounce through spostgre).
- Used for: checkpoint compaction (fold live page-versions into the sealed arena), snapshot materialization (M4+).
- **Atomicity:** clone is not atomic; spostgre sequences clone → pmap update → old-arena discard.

### S5. Preferred I/O granule + capability query (load-bearing, P0)

```
fn fs_caps() -> FsCaps

struct FsCaps:
    preferred_write_granule: u32       # bytes; WAL align target
    atomic_write_unit_power: u32       # AWUPF; page-atomic threshold
    supports_cas: bool                 # fused Compare-and-Write available
    supports_zns: bool
    supports_fdp: bool
    supports_copy_offload: bool
    supports_flush_fua: bool
    write_amp_hint: f32                # device-reported or estimator
    mount_generation: u64              # bumps on every mount
```

- spostgre caches `FsCaps` at mount and refreshes at each checkpoint (5–60 s cadence). Changes between refreshes are safe — spostgre never assumes a capability it did not observe at cache time.
- **Failure modes:** none; query is infallible once mounted.

### S6. Capability-gated atomic-pointer-record publish (load-bearing, P0)

```
fn atomic_pointer_record_publish(
    scope: RecordScope,
    name: StaticStr,
    bytes: Slice<u8>,
    expected_gen: Option<Generation>
) -> Result<PublishResult, FsErr>
```

- Publish `bytes` under `(scope, name)`. If `expected_gen = Some(g)` and the stored generation differs, fail with `CasMismatch(actual_gen)`. Otherwise bump generation and return the new one in `PublishResult`.
- On devices with fused Compare-and-Write (`fs_caps().supports_cas == true`), NVFS implements this as a single fused NVMe op; otherwise it uses a double-buffered intent-log with a sequence number (research §11.5 + research OQ-14).
- spostgre uses this for pmap-root atomic swap at checkpoint commit. svllm uses it for manifest flip. **This is convergence candidate C1** — NVFS must not fork into two APIs.
- **Failure modes:** `CasMismatch` (caller retries), media error (caller aborts commit).

### S7. NVMe Flush / FUA pass-through tied to durability classes (load-bearing, P0)

```
fn arena_flush(arena: ArenaId) -> Result<(), FsErr>                             # Flush semantics; metadata+data durable
fn arena_fua_append(arena: ArenaId, bytes, granule) -> Result<Offset, FsErr>    # per-op FUA
```

- `arena_flush` maps to NVMe Flush. On volatile-write-cache-disabled drives, NVFS may return immediately.
- `arena_fua_append` sets the FUA bit on the underlying write; for devices without the bit, NVFS falls back to `append + flush`.
- spostgre's `Durability::DURABLE_ON_RETURN` maps to `arena_fua_append`; `DURABLE_GROUP_COMMIT` maps to `arena_append + arena_flush` with coalescing (see S2).

---

## Desired but not required (stretch, P1)

### S-stretch-1. ZNS zone-append for WAL

- If `fs_caps().supports_zns`, NVFS may implement `arena_append_aligned` on `DB_WAL` using `Zone Append` (implicit offsets, no head-of-line blocking). spostgre must not assume this — the returned offset is still monotonic in either mode.

### S-stretch-2. FDP PIDs per storage class

- If `fs_caps().supports_fdp`, NVFS maps each `StorageClass` to a distinct Placement ID so device-side GC can separate WAL from page-main from temp. spostgre benefits without changing its API usage.

### S-stretch-3. Namespace-per-class

- On multi-namespace controllers, NVFS may dedicate a namespace per class, delivering hardware-level isolation (most powerful but rarely available). spostgre takes this as a pure perf win.

### S-stretch-4. Copy offload for arena_clone_range

- If `fs_caps().supports_copy_offload`, implement S4 via NVMe `Copy`; halves host CPU + halves bus traffic for checkpoint compaction.

### S-stretch-5. CMB / PMR for WAL buffers

- If exposed, NVFS may register the WAL in-flight buffer in CMB (commit-latency reduction). spostgre is indifferent at the API level.

### S-stretch-6. Dataset Management (DSM) trim on arena_discard

- NVFS SHOULD issue DSM trim when a discarded arena's LBAs are released back to the free pool. spostgre does not observe this directly but benefits via sustained WAF.

---

## Non-requirements (explicit, to help NVFS scope)

spostgre does **not** need these; NVFS need not implement them for spostgre's sake:

- **POSIX permissions / ACLs.** spostgre is one trusted process; capability-based access through the spostgre capsule is sufficient.
- **Hard links, symlinks.** Arena IDs are the only naming level spostgre uses.
- **Case-insensitive paths.** spostgre names arenas by `(relation_oid, fork_tag, epoch)`, never by user-supplied strings.
- **xattrs.** All metadata spostgre needs is in its own catalog (`META_DURABLE` arena).
- **mmap semantics.** spostgre reads explicitly; no page-fault-driven I/O at M1.
- **Concurrent writers on one arena.** spostgre serializes writers per arena; WAL has at most one active writer via a per-node lock.
- **Rename across classes.** An arena's class is set at create-time and never changes.
- **Sub-arena deletion.** Arenas are discarded wholesale; no range-free inside an arena.
- **Fsync-on-close for every arena.** spostgre calls `arena_flush` / `arena_seal` explicitly.
- **Crash-consistent `arena_create`.** If `arena_create` crashes mid-creation, NVFS may garbage-collect orphan arenas at mount; spostgre will re-create on the next operation.

---

## Performance budget (approximate, to be refined by measurement)

| Operation | Target p50 | Target p99 | Dominant cost |
|---|---|---|---|
| `arena_append_aligned` (4 KiB, DURABLE_GROUP_COMMIT, batch of 8) | ≤ 80 µs | ≤ 400 µs | NVMe Flush latency |
| `arena_append_aligned` (64 KiB, BUFFERED) | ≤ 20 µs | ≤ 100 µs | memcpy + submission |
| `arena_read` 8 KiB (buffered cache hit in NVFS) | ≤ 5 µs | ≤ 30 µs | memcpy |
| `arena_read` 8 KiB (NVMe read) | ≤ 50 µs | ≤ 300 µs | NVMe latency |
| `atomic_pointer_record_publish` (CAS path, 64 B) | ≤ 100 µs | ≤ 500 µs | Fused op |
| `atomic_pointer_record_publish` (intent-log fallback) | ≤ 400 µs | ≤ 2 ms | Two writes + flush |
| `arena_seal` | ≤ 500 µs | ≤ 2 ms | Metadata flush |
| `arena_discard` (after pinning clears) | ≤ 100 µs | ≤ 1 ms | Metadata bump + DSM submit |
| `arena_clone_range` 8 KiB (copy offload) | ≤ 40 µs | ≤ 200 µs | NVMe Copy latency |
| `arena_clone_range` 8 KiB (fallback) | ≤ 100 µs | ≤ 500 µs | Read + write |

These are single-node, single-drive, steady-state after SSD-iq preconditioning (research §8). NVFS is free to miss these numbers at baseline but should document the gap.

---

## Interaction with runtime families

- **M1–M2 (nogc_sync_mut):** spostgre issues all NVFS calls synchronously from the engine's WAL-writer thread and checkpoint thread. NVFS may still coalesce internally, but spostgre sees blocking calls.
- **M3 (nogc_async_mut):** spostgre introduces an AIO path (io_uring_cmd). NVFS must offer an async variant of `arena_read` / `arena_append_aligned` that returns a completion handle. Signatures to be defined in a later revision of this doc; for now, document the migration plan in §Open coordination.
- **M4+ (nogc_async_mut):** async checkpoint, async vacuum. No new NVFS primitives needed — same async variants as M3.

spostgre never uses `gc_async_mut` or `nogc_async_mut_noalloc` against NVFS.

---

## Alignment with research doc and design docs

| Research section | This doc section | spostgre design section |
|---|---|---|
| §6 Multiple Atomicity Mode, AWUPF | S5, §Workload profile | §6 WAL protocol |
| §7 io_uring_cmd, SPDK | §Interaction with runtime families | §9 out-of-place write pipeline |
| §8 SSD-iq benchmarking | §Workload profile, §Perf budget | §12 Phased milestones ACs |
| §11.1 Per-fork class hint | S1 | §4 on-disk layout |
| §11.2 Aligned-append WAL | S2 | §6 WAL protocol |
| §11.3 Sealed checkpoint arenas | S3 | §10 Recovery |
| §11.4 arena_clone_range | S4 | §9 write pipeline compact step |
| §11.5 Capability-probed CAS | S6 | §6 WAL + §10 Recovery |
| §11.6 Preferred I/O granule | S5 | §6 WAL protocol |

---

## Open coordination questions for the nvfs agent

1. **Naming of the atomic-pointer primitive.** `atomic_pointer_record_publish` is verbose. Alternatives: `fs_publish_atomic`, `slot_cas_publish`, `named_record_publish`. Pick one; spostgre will follow.
2. **Per-op durability flag vs per-arena policy.** spostgre prefers per-op (S2's `Durability` enum). svllm's R4 prefers per-open-handle default with per-op override. Can both be served by a single API with `Durability::INHERIT` as the default?
3. **AIO signatures.** When spostgre reaches M3, what is the NVFS async API shape? io_uring completion entries? Simple's actor mailboxes? Decide before M3 so spostgre's AIO plan is concrete.
4. **Generation-number width.** spostgre needs 64-bit generations (commit LSNs are 64 bit). Confirm NVFS's `Generation` type is `u64`.
5. **SealToken opacity.** Is `SealToken` a `u64` (opaque ID) or a struct carrying generation + checksum? spostgre prefers opaque; reveal only what `arena_discard`'s `keep_gen_above` needs.
6. **DB_TEMP drop-on-mount.** spostgre needs this for hash-build / sort-spill — temp arenas MUST be discarded at every fresh mount. Confirm NVFS guarantees this in its recovery path.
7. **Multi-drive mount.** If NVFS spans two NVMe drives, does spostgre see one logical arena space or must it issue per-drive calls? spostgre prefers single logical space; NVFS handles striping.
8. **Capability-probe caching window.** spostgre re-reads `FsCaps` at every checkpoint. Is that too infrequent (mid-mount hot-plug) or too frequent (wasted probe)? Propose a cadence.
9. **Reconciliation with svllm_requirements.md.** Please produce a single NVFS design (§11 of `../nvfs_design.md`) that serves both without two API surfaces. Call out any conflict you find so spostgre can negotiate.
10. **ZNS-only mode.** If NVFS is mounted on a pure-ZNS drive, does `GENERAL_MUTABLE` have meaningful semantics or does it degrade to copy-on-seal like `MODEL_IMMUTABLE`? Answer drives spostgre's rel.main placement.
