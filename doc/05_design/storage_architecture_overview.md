# SimpleOS Storage Architecture — Overview

> **Status:** living overview, 2026-04-18.
> **Audience:** new contributors needing a map before diving into any one layer.
> **Rule:** this doc is a reader's guide, not a spec. Authoritative details live in
> the linked per-layer docs.

---

## 1. The Stack in One Diagram

```
 ┌──────────────────────────────────────────────────────────────┐
 │  Applications (svllm, user services, POSIX tools, Rust FFI)  │
 └─────────────────┬─────────────────────────┬──────────────────┘
                   │ SQL / page API           │ POSIX (open/read/write/mmap)
 ┌─────────────────▼──────────┐ ┌────────────▼──────────────────┐
 │        spostgre            │ │      NVFS POSIX shim           │
 │   (MDSOC+ / ECS inside)    │ │   (DriverInstance::NvfsPosix)  │
 │  doc/05_design/spostgre_   │ │  doc/05_design/nvfs_posix_     │
 │  design.md                 │ │  wrapper.md                    │
 └─────────────────┬──────────┘ └────────────┬──────────────────┘
                   │ S1–S7 arena API           │ arena API
 ┌─────────────────▼───────────────────────────▼──────────────────┐
 │                    FsDriver trait + MountTable                   │
 │   (Option E' enum dispatch — no dyn, no generics in mount list) │
 │         doc/05_design/fs_driver_interface.md                    │
 └──────────┬─────────────────┬──────────────────┬────────────────┘
            │                 │                  │
 ┌──────────▼──────┐ ┌────────▼──────┐ ┌────────▼──────┐
 │   NVFS (native) │ │  FAT32Driver  │ │   RamFs (dev) │
 │ DriverInstance  │ │ DriverInstance│ │ DriverInstance│
 │ ::Nvfs          │ │ ::Fat32       │ │ ::Ram         │
 │                 │ │               │ │               │
 │ doc/05_design/  │ │ (C externs    │ │ (in-memory    │
 │ nvfs_design_v2  │ │  rt_fat32_*)  │ │  arena pool)  │
 │ .md             │ │               │ │               │
 └──────────┬──────┘ └───────────────┘ └───────────────┘
            │
 ┌──────────▼──────────────────────────────────────────────────────┐
 │             Block device / NVMe namespace                        │
 │  Capability-probed features: ZNS  FDP  CMB  PMR                 │
 └─────────────────────────────────────────────────────────────────┘
```

---

## 2. Reader's Guide — "If you want X, read Y"

| Goal | Start here |
|------|-----------|
| Understand the full NVFS design (B-tree forest, pmap, Merkle, snapshots) | [`nvfs_design_v2.md`](nvfs_design_v2.md) |
| Understand how spostgre stores pages on NVFS | [`spostgre_design.md`](spostgre_design.md) §2–§6 |
| See which NVFS APIs spostgre requires (S1–S7 contract) | [`nvfs/from_spostgre.md`](nvfs/from_spostgre.md) |
| Understand how any FS plugs into SimpleOS (FsDriver trait, mount table, Extension enum) | [`fs_driver_interface.md`](fs_driver_interface.md) |
| Understand how POSIX callers (libc, tools) sit above NVFS | [`nvfs_posix_wrapper.md`](nvfs_posix_wrapper.md) |
| Track the FAT32 → NVFS migration plan (paths A/B/C, vfs_init chokepoint) | [`simpleos_fs_migration.md`](simpleos_fs_migration.md) |
| Wire format for NVFS send/receive (NVSR stream, encryption flag, arena records) | [`nvfs/send_format.md`](nvfs/send_format.md) |
| MDSOC+ architecture that governs all of the above | [`../04_architecture/mdsoc_architecture_tobe.md`](../04_architecture/mdsoc_architecture_tobe.md) |

---

## 3. Architecture Decisions That Cut Across Docs

### 3.1 Why MDSOC+ for spostgre but MDSOC-only for NVFS

The Layer Rules table in `mdsoc_architecture_tobe.md` distinguishes:

- **Kernel-adjacent code** (drivers, VFS, FS implementations): MDSOC-only. No ECS.
  The scheduler cannot run ECS systems inside an interrupt or a page-fault handler.
  NVFS is in this category.

- **Userland services and apps**: MDSOC outer + ECS business layer (MDSOC+).
  spostgre is a userland service — its internal state (relations, tuples, WAL records,
  buffer frames) is a natural ECS world. The outer MDSOC capsule provides capability
  tokens, port contracts, and lifecycle; the inner ECS world provides change-detection
  and composable systems (`sys_commit`, `sys_wal_flush`, `sys_buffer_manager`, …).

### 3.2 No `dyn` — Option E' dispatch

Simple's `nogc_sync_mut` layer has no allocator and prohibits virtual dispatch.
The mount table holds a `Vec<MountEntry>` where each entry wraps a `DriverInstance`
enum variant. All dispatch is exhaustive `match`. Adding a new FS type adds a new
enum variant; the compiler flags every unhandled arm. See `fs_driver_interface.md §1`.

### 3.3 The arena model

NVFS is append-only at the physical layer. Every write creates a new arena; arenas
are immutable once sealed. This is the key design choice that enables:

- Out-of-place updates (spostgre never mutates a page in place — it appends a new
  page arena and bumps `rel.pmap`).
- Copy-on-write snapshots and block cloning (N6).
- POSIX random-write via the shim (read → modify → new arena → publish → discard old).
- ZNS/FDP zone alignment (arenas map 1:1 to zones or FDP reclaim units).

### 3.4 Upfront API contributions

Each upstream consumer of NVFS filed a requirements document before NVFS was designed:

- **spostgre** filed S1–S7 in `nvfs/from_spostgre.md`.
- **svllm** filed R1–R9 in `nvfs/svllm_requirements.md` (note: svllm explicitly does
  NOT need POSIX semantics).

The NVFS designer reconciled both in one pass. Post-hoc requests go to
`doc/08_tracking/feature_request/nvfs_requests.md` (secondary channel).

---

## 4. Feature Gates and Capability Probes

All four hardware features are probed at mount time. NVFS falls back gracefully if a
feature is absent. spostgre placement hints are advisory; the engine works on plain NVMe.

| Feature | What it enables | Where designed |
|---------|----------------|----------------|
| **ZNS** (Zoned Namespace) | Per-storage-class zone placement; sequential-write guarantee eliminates GC write amplification | `nvfs_design_v2.md` §ZNS; spostgre M5 (`spostgre_design.md §1.1`) |
| **FDP** (Flexible Data Placement) | RUH-per-fork placement (WAL fork vs. data fork land in separate reclaim units) | `nvfs_design_v2.md` §FDP; `nvfs/from_spostgre.md` S5 |
| **CMB** (Controller Memory Buffer) | Zero-copy DMA for WAL arenas; `arena_append` bypasses host DRAM on CMB-capable devices | `nvfs_design_v2.md` §CMB |
| **PMR** (Persistent Memory Region) | Crash-consistent staging for checkpoint ring; eliminates double-write on superblock flush | `nvfs_design_v2.md` §PMR |

---

## 5. SimpleOS FS Migration

SimpleOS currently has three execution paths (A, B, C). The migration consolidates
everything into Path C (the FsDriver/MountTable design). Path A (direct `rt_fat32_*`
C externs) is re-routed through MountTable. Path B (old `Filesystem` trait) is retired.

Migration entry point: `src/os/services/vfs/vfs_init.spl`.

Details: [`simpleos_fs_migration.md`](simpleos_fs_migration.md).

---

## 6. Wire / Replication

The NVFS send stream (NVSR) transports sealed arenas between peers. Milestone N6b.
16-byte leading header (magic `NVSR`, version, flags, arena_count, checksum_algo).
Ciphertext travels verbatim; only the dataset-key holder can mount the received arena.

Details: [`nvfs/send_format.md`](nvfs/send_format.md).

---

## 7. Source Locations

| Layer | Trait contracts | Implementation |
|-------|----------------|----------------|
| FsDriver trait + MountTable | `src/lib/nogc_sync_mut/fs/` | n/a (trait only) |
| NVFS native | `src/lib/nogc_sync_mut/fs/nvfs/` | `examples/nvfs/src/core/` |
| NVFS POSIX shim | `src/lib/nogc_sync_mut/fs/nvfs/` | `examples/nvfs/src/posix/` |
| spostgre | `src/lib/nogc_sync_mut/spostgre_if/` | `examples/spostgre/src/engine/` |
| FAT32 (C runtime) | `src/os/services/vfs/` | `src/os/arch/x86_64/fat32/` |

---

## 8. Milestones Summary

### NVFS
| Milestone | Summary |
|-----------|---------|
| N1 | Superblock, checkpoint ring, arena_* API, pmap v1 |
| N2 | WAL arena, storage-class placement |
| N3 | Snapshots, subvolumes, tree-sharing |
| N4 | Scrub + repair (N4a peer scan; N4b scheduler + META_DURABLE fallback) |
| N5 | ZNS/FDP/CMB/PMR capability probes |
| N6 | Send/receive (N6b raw + encrypted), block cloning (N6c) |
| N7 | Native encryption (dataset key, per-chunk RAID) |
| N8 | ARC caching, deduplication |

### spostgre
| Milestone | Summary |
|-----------|---------|
| M1 | Sync engine, WAL, BRIN index, pmap v1 (nogc_sync_mut) |
| M2 | Out-of-place page writes, wire protocol (libpq-compatible) |
| M3 | BRIN-HOT-logical, AIO (nogc_async_mut) |
| M4 | Tiered cache, cost-model rework |
| M5 | ZNS/FDP per-fork placement |

### SimpleOS FS Migration
| Milestone | Summary |
|-----------|---------|
| FM1 | Fat32Driver impl behind MountTable; Path A re-routed |
| FM2 | Path B (old Filesystem trait) retired |
| FM3 | NVFS native driver mounted alongside FAT32 |
| FM4 | Boot volume migrated to NVFS |
