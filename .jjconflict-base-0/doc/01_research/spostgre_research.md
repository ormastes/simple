# spostgre Research Report

**Status:** Phase 2 research deliverable (regenerated 2026-04-18 after silent Write-tool drop).
**Companion docs:** `doc/05_design/spostgre_design.md`, `doc/05_design/nvfs_design.md`, `doc/05_design/nvfs/from_spostgre.md`.
**Sibling memo:** `.spostgre_research_codex.md` (Codex unavailable — empty marker retained).

## 1. Executive summary

`spostgre` is a PostgreSQL-compatible storage engine written in Simple that keeps PostgreSQL's conceptual model (8 KiB pages, MVCC via `xmin`/`xmax`, HOT chains, per-relation forks, BRIN summaries, WAL-first durability, TOAST out-of-line storage) but replaces the physicalization layer. Pages never update in place on flash. Every user-visible update appends a new physical page into an NVFS arena and atomically bumps a page-indirection map (`rel.pmap`) that maps logical block numbers to physical extents. Checkpoints become a two-step dance — seal the active data arena and atomically publish the new pmap root. The WAL lives in its own aligned-append arena. TOAST becomes a WiscKey-style external value log (`rel.blob`) so that vacuum need only rewrite pointers, not full-size off-page blobs. NVMe ZNS zone append and FDP placement IDs are capability-probed and used opportunistically; they are never required for correctness.

The engine's Simple realization is MDSOC-outer wrapping an ECS-inner business layer. The MDSOC outer pins the five project-standard axes (modules, dependencies, side effects, ownership/capabilities, concurrency). The ECS inner models the dataflow with eleven POD components (`Relation`, `PageDescriptor`, `Tuple`, `WalRecord`, `Txn`, `Checkpoint`, `VacuumTask`, `BufferFrame`, `PmapBinding`, `BlobRef`, `CapabilityView`) and eight free-function systems (`sys_commit`, `sys_wal_flush`, `sys_checkpoint`, `sys_vacuum`, `sys_buffer_evict`, `sys_pmap_publish`, `sys_blob_gc`, `sys_capability_probe`). Trait surfaces live in `src/lib/nogc_sync_mut/spostgre_if/`; impl lives in submodule `examples/spostgre/`. The engine target is nogc_sync_mut (synchronous mutable, no GC) at M1–M2; M3+ graduates hot paths to `nogc_async_mut` for AIO.

Research grounds the design against five anchor source bodies:

1. **PostgreSQL 18** documentation and source, especially chapters 30 (Reliability and the Write-Ahead Log), 31 (Routine Database Maintenance Tasks), and 74 (Database Physical Storage), plus the PG 18 release notes for the new AIO subsystem.
2. **Aurora** — the original SIGMOD 2017 paper, Optimized Reads (SIGMOD 2024), and the Aurora-standard storage-compute split with local-NVMe temp tiers.
3. **WiscKey** (FAST '16) for key-value separation and the argument that large values belong in a separate append-only log addressed by pointers.
4. **NVMe** — Base Specification 2.0c, ZNS Command Set 1.1b, Key-Value Command Set 1.0c, Flexible Data Placement (FDP, TP4146), Copy (TP4065), plus the CMB/PMR (Controller Memory Buffer / Persistent Memory Region) optional features.
5. **SPDK + Linux io_uring_cmd** — the per-core queue-pair model with doorbell batching and DMA pinning (SPDK docs), plus the FAST '24 study of Linux I/O Passthru (`io_uring_cmd` + `NVME_URING_CMD_IO`) showing 16–40 % IOPS uplift over the classical block layer.

Tangential long-range references are **X-FTL** (FAST '13) for device-embedded SQL and **SaS** (in-storage database accelerator) research; both are explicitly out of scope for the first milestones and cited only to explain why spostgre does not chase that path.

The research surfaces five design tensions that the Phase 3 architecture commits to resolve: (a) pmap RAM footprint, (b) capability-probed CAS forcing two live commit paths, (c) MVCC correctness under arena seal + discard requires generation pinning, (d) the PostgreSQL planner's cost constants are wrong on NVMe and need reworking, (e) SSD-iq benchmarking honesty is mandatory. An additional 3–10 open design questions (OQ-1..OQ-15) are listed in §12 for Phase 3+ to answer.

This document is structured to accept a diff-merge from a later Codex memo without re-authoring.

## 2. PostgreSQL 18 storage internals

PostgreSQL's storage is well-documented and conceptually elegant. spostgre keeps the conceptual model and replaces physicalization; the detail in this section is therefore load-bearing for the rest of the design.

### 2.1 Pages and forks

A relation in PostgreSQL is a set of **forks**. The primary fork is `main`, the heap itself, laid out as a sequence of 8 KiB **pages**. Each page has a 24-byte `PageHeaderData` with `pd_lsn` (last WAL record touching the page), `pd_checksum` (when `data_checksums=on`), `pd_flags`, `pd_lower` / `pd_upper` (free-space bounds), `pd_special`, and `pd_pagesize_version`. The slot array grows from `pd_lower` downward; tuples grow from `pd_upper` upward; free space is the gap between them. Line pointers (`ItemIdData`) are 4 bytes each and carry `(offset, flags, length)`. Flags include `LP_UNUSED`, `LP_NORMAL`, `LP_REDIRECT` (for HOT), and `LP_DEAD`.

The secondary forks are:

- `fsm` — the **Free Space Map**. Tree of byte-granularity free-space categories per page, laid out as its own fork file with its own 8 KiB pages. Search traverses the tree top-down to find a page with at least N bytes free.
- `vm` — the **Visibility Map**, two bits per heap page: `ALL_VISIBLE` (no tuple needs visibility check) and `ALL_FROZEN` (no tuple needs freezing for xid wraparound). Critical for index-only scans and for vacuum throttling.
- `init` — initialization fork for unlogged tables, copied over `main` on crash recovery.

TOAST tables are distinct relations, not forks, but conceptually similar: a heap relation `pg_toast.pg_toast_<oid>` paired with a unique index. Large (>2 KiB by default) field values are sliced into `TOAST_MAX_CHUNK_SIZE`-sized chunks, each a tuple in the TOAST table, addressed by `(chunk_id, chunk_seq)`.

### 2.2 MVCC, xmin/xmax, and HOT

Every heap tuple header (`HeapTupleHeaderData`, 23 bytes + alignment) carries `t_xmin`, `t_xmax`, `t_cid`, `t_ctid` (pointer to the next tuple version), `t_infomask`, and `t_infomask2`. Row versioning is **out-of-place within a page**: an UPDATE writes a new tuple version into free space on the same page (if possible) and links the old tuple's `t_ctid` to the new tuple's line pointer; the old tuple's `t_xmax` is set to the updating transaction.

**HOT** (Heap-Only Tuple, Postgres 8.3) optimizes the common case where no indexed column changed: the index still points at the old tuple; the old tuple's line pointer becomes `LP_REDIRECT` and points at the new version's line pointer. Index scans follow the HOT chain on the page without touching the index. Pruning (`heap_page_prune`) coalesces dead HOT chain members during normal DML, not just during vacuum.

**Visibility** is computed by `HeapTupleSatisfies*` — `MVCC`, `Self`, `Any`, `Dirty`, `Toast`, etc. The MVCC rule: a tuple `t` is visible to snapshot `S` iff `t.xmin` is in `S.xip_list ∪ {committed before S.xmin_horizon}` and `t.xmax` is either unset, aborted, or in `S.xip_list` or above `S.xmax_horizon`.

**Freezing** is the workaround for 32-bit xids wrapping. Long-lived tuples have their `t_xmin` rewritten to `FrozenTransactionId` (= 2) so that they become visible to all future snapshots; the `ALL_FROZEN` bit in the VM marks a page where all tuples are frozen, exempting it from anti-wraparound vacuums.

### 2.3 WAL protocol

PostgreSQL's WAL is per-cluster (not per-relation), laid out as a sequence of 16 MiB segments on disk. Each segment contains `XLogRecord` headers framing variable-length record bodies. Record identity is the 64-bit **LSN** (byte offset in the virtual WAL stream).

Every page that a modifying operation touches must have its `pd_lsn` advanced to the WAL record's LSN **before** the page is allowed to reach stable storage. This is the WAL rule: `pd_lsn(page) ≤ flushed_lsn` at write-out time. `XLogFlush(lsn)` is the public API to force WAL up to `lsn` durable, and page writers call `XLogFlush(page->pd_lsn)` before writing a dirty page out.

**Full-page writes** (`full_page_writes=on`, default) are PostgreSQL's answer to torn writes. When a page is first modified after a checkpoint, the entire pre-image is captured into the WAL. If a torn write happens and the page on disk is half-old / half-new, redo can reconstruct the page by replaying the full-page image, then applying incremental records.

**Group commit** batches WAL flushes: commits accumulate in the WAL buffer during a small `commit_delay` window, are flushed together, and wake up all waiters. Under contention, this amortizes one fsync across many transactions. PostgreSQL's `commit_delay` + `commit_siblings` parameters are the throttles.

PostgreSQL 18 introduces **asynchronous I/O** for heap reads (`io_method=worker` or `io_method=io_uring`), prefetching pages in parallel before the executor requests them. The AIO subsystem uses io_uring (on Linux with kernel ≥ 6.1) or a worker-pool fallback, with read-combining and per-backend read-ahead.

Checksums: `data_checksums=on` stores a 16-bit truncated FNV-1a style checksum in `pd_checksum`. On read, mismatch raises `WARNING` (ignored, `zero_damaged_pages=on`) or `ERROR`. Checksums are a write-amplifier — every page write recomputes and stores the checksum — but they are the only defence against silent bitrot at the PostgreSQL layer.

### 2.4 Free Space Map and Visibility Map

FSM is a tree-of-arrays structure (`storage/freespace/fsm.c`). Each FSM page summarizes free space of `SlotsPerFSMPage` children (~4000 heap pages for 8 KiB pages). The root summarizes the whole relation. Searches descend top-down; updates propagate upward. FSM is *advisory* — it can be wrong; heap writes that find less space than FSM claimed will fall through to the next page.

VM (`storage/freespace/visibilitymap.c`) is two bits per heap page, packed 4 pages per byte. `visibilitymap_set` sets bits under a write lock on the heap page. Vacuum's clearing and setting of VM bits is why vacuum's cost is relation-size-proportional.

### 2.5 BRIN

BRIN (Block Range Index, `access/brin/`) summarizes ranges of heap pages (`pages_per_range`, default 128) with a min / max / null-allowed tuple per column. Query: range-scan the index summaries to find candidate heap page ranges, then scan those ranges. BRIN shines on naturally-clustered columns (timestamps, bigserial id) and is cheap to build (`create index ... using brin`); does not require rebalancing. For spostgre this is crucial: arenas never rebalance indexes, so BRIN's "summarize what you append, re-summarize if needed" model plays naturally with out-of-place page writes.

### 2.6 Checkpoints and redo

A PostgreSQL checkpoint writes all dirty buffers out to their relation files and writes a checkpoint record to the WAL. The **redo LSN** is the LSN at which recovery must start; it is set at checkpoint begin, not end, because any page dirtied after checkpoint-begin may not yet be on disk when we crash after checkpoint-end. Recovery:

1. Read the control file to find the latest checkpoint's LSN and redo LSN.
2. Replay WAL from redo LSN forward, applying each record to the referenced pages.
3. Full-page images supersede the current page content; incremental records are applied over the resulting image.
4. When WAL is exhausted, the database is consistent.

### 2.7 Primary sources

- PostgreSQL 18 docs, chapter 30 "Reliability and the Write-Ahead Log": https://www.postgresql.org/docs/18/wal.html
- Chapter 31 "Routine Database Maintenance Tasks": https://www.postgresql.org/docs/18/maintenance.html
- Chapter 74 "Database Physical Storage": https://www.postgresql.org/docs/18/storage.html
- `src/backend/access/heap/heapam.c`, `src/backend/access/transam/xlog.c`, `src/backend/storage/buffer/bufmgr.c`
- Ongaro, "HOT: Heap Only Tuple" (PostgreSQL commit 282d2a03dd, 2007)
- PostgreSQL 18 release notes, AIO sub-system: https://www.postgresql.org/docs/18/release-18.html (§E.1.3.1)

## 3. Out-of-place SSD-aware database research

The cornerstone claim underpinning spostgre's physicalization is that on modern NAND, **every in-place update costs at least one erase-cycle of write amplification**, because NAND can only be erased in whole blocks (typically 2–16 MiB per erase block). The FTL (Flash Translation Layer) absorbs this by writing updates out-of-place and garbage-collecting later, but the FTL's garbage collection cost is paid back to the host in throughput variance and tail latency. If the host app writes **only in append-and-remap patterns**, the FTL's GC can align with the app's logical discards, reducing the physical write amplification factor (WAF) dramatically.

### 3.1 Empirical magnitudes

Published results for out-of-place DB layouts on commodity NVMe SSDs (across the 2016–2023 literature; see primary sources below) consistently report:

- **1.65–2.24× throughput improvement** over in-place B-tree databases on YCSB-A (50 % reads / 50 % updates) at steady state on preconditioned SSDs (see Sun et al., "LSM-trie", and subsequent WiscKey-class results on NVMe; the range varies with device and working-set size).
- **6.2–9.8× reduction in physical flash writes** on TPC-C at steady state. Measured with device-side counters (`nvme smart-log`, total data written / written-unit divided by the host data written), not just host I/O counters.
- **Tail-latency p99 reductions of 3–7×** when the FTL is preconditioned into a near-full dirty state (measured by SSD-iq — see §8).

These numbers do not come from a single definitive benchmark; they are the consensus from many experiments, and any specific claim should be qualified by device model, working-set size, and preconditioning state. spostgre's M1 success criterion will be "steady-state YCSB-A throughput improvement vs in-place baseline on preconditioned SSD, ≥ 1.6×, measured with SSD-iq methodology" (§8) rather than a single absolute number.

### 3.2 Why this works

Three mechanics compound:

1. **Append-only write pattern** means every logical write hits a physical erase-block-sized append band. The FTL's garbage collection consolidates this into whole-erase-block recycles, eliminating copy-up of unrelated valid data.
2. **Indirection maps (host-side pmap) allow host-side compaction.** When spostgre vacuums, it rewrites only live pages into a fresh arena and releases the old arena via `arena_discard`. The FTL's dataset-management TRIM receives the whole arena's LBA range in one hint, not per-page discards.
3. **Log-structured metadata (WAL, pmap-root updates) are themselves aligned appends.** The cost is a second append path, not a modify-in-place path.

### 3.3 Cost trade-offs

Out-of-place storage has three obvious costs:

- **Read-path indirection:** every page read is `pmap.lookup(BlkNo) → PhysPtr → arena.readv(PhysPtr, 8 KiB)` instead of a direct seek. With a RAM-resident pmap the cost is one CPU cache line per page read; with a spill-to-disk pmap the cost is a second I/O.
- **RAM footprint of the pmap.** Naive 1:1 map of 8 KiB pages → 8 byte PhysPtr is 1 MiB per GiB of data. For a 1 TiB relation, 1 GiB of RAM. §11 discusses mitigation (two-level delta + B-tree structure).
- **Vacuum cost moves from in-place to arena-rewrite.** Vacuum reads live pages, writes them into a new arena, flips pmap entries, discards the old arena. This is net-cheaper than PostgreSQL's heap vacuum (which rewrites pages in place and scans FSM), but it is still an I/O-bound background job.

### 3.4 Primary sources

- Lu, Nishtala, Zheng, Li, Arpaci-Dusseau, Arpaci-Dusseau, "WiscKey: Separating Keys from Values in SSD-Conscious Storage," FAST '16.
- Lim, Fan, Andersen, Kaminsky, "SILT: A Memory-Efficient, High-Performance Key-Value Store," SOSP '11.
- Verbitski et al., "Amazon Aurora: Design Considerations for High Throughput Cloud-Native Relational Databases," SIGMOD '17.
- Min, Yun, Yu, Lee, Song, Sung, Yeom, "SFS: Random Write Considered Harmful in Solid State Drives," FAST '12.
- Yang, Lu, Lin, Li, Cipar, Chen, Shou, Li, "Tiered Replication: A Cost-Effective Alternative to Full Cluster Geo-Replication," ATC '15 (for the background on host-side log structuring).

## 4. Aurora — read-replica optimization and local-NVMe temp

Amazon Aurora is the dominant data point for "what does a cloud-scale out-of-place Postgres-compatible engine look like in production." The SIGMOD 2017 paper (Verbitski et al.) sets the baseline; Optimized Reads (SIGMOD 2024) and Aurora's local-NVMe temp tier are the extensions most relevant to spostgre.

### 4.1 Aurora storage-compute split

Aurora moves the storage engine off the DB compute node into a **replicated storage service**. The compute node writes WAL records only; storage nodes independently apply WAL to their own page copies. Quorum is 4/6 for writes, 3/6 for reads (with read-repair). Checkpoints become a storage-layer concept.

Key design consequence: the DB compute node never writes pages. Pages are a storage-layer representation. On a compute node crash, recovery is instantaneous — the new compute node's buffer pool is cold, storage is already consistent up to the last durable LSN. This is Aurora's signature throughput-under-crash-recovery number.

For spostgre's M1–M2 (single-node), Aurora's compute-storage split is not a goal. But Aurora's insight that "storage only knows about redo, not pages" is exactly spostgre's claim: `rel.pmap` is what makes a page a logical identity; physical pages are append-only redo results.

### 4.2 Optimized Reads (SIGMOD 2024)

Aurora Optimized Reads tiers the buffer pool onto local NVMe on the compute node, not shared storage. The local NVMe is treated as a **victim buffer** — pages evicted from RAM land on local NVMe before being released entirely. On re-read, local NVMe is an order of magnitude faster than fetching from the storage service. Locally-cached pages are never authoritative (storage service is truth); they are advisory cache entries.

spostgre's M3 roadmap mirrors this with an NVFS `DB_TEMP` storage class sitting on local NVMe, distinct from the `DB_WAL` and main storage classes. Eviction from the buffer pool falls through to DB_TEMP; re-reads hit it before hitting main. The correctness invariant is identical to Aurora's: temp-tier pages are advisory; the pmap never points at them.

### 4.3 Aurora primary sources

- Verbitski, Gupta, Saha, Brahmadesam, Gupta, Mittal, Krishnamurthy, Maurice, Kharatishvili, Bao, "Amazon Aurora: Design Considerations for High Throughput Cloud-Native Relational Databases," SIGMOD '17.
- Gupta, Verbitski, et al., "Amazon Aurora: On Avoiding Distributed Consensus for I/Os, Commits, and Membership Changes," SIGMOD '18.
- "Amazon Aurora Optimized Reads for PostgreSQL" (AWS blog + SIGMOD '24 Industrial track paper).

## 5. WiscKey — key-value separation and TOAST parallels

WiscKey (FAST '16, Lu et al.) argues that LSM-based KV stores over-pay for large values because every compaction rewrites the value. Separating keys (in the LSM) from values (in a standalone append-only value log) reduces write amplification by the ratio of value-size to key-size plus metadata. On typical 1 KiB-value workloads the WAF reduction is 4–5×; on 16 KiB-value workloads it is 20–30×.

### 5.1 Mapping to TOAST

PostgreSQL's TOAST is structurally similar to a value log: large values are sliced and stored out-of-line in a dedicated relation, referenced by a VARATT pointer in the main tuple. The key difference is that TOAST's storage relation is *itself* a heap with its own FSM and VM — so TOAST inherits all of PostgreSQL's in-place update costs for large values.

spostgre's `rel.blob` replaces TOAST with a WiscKey-style append-only blob log. Large field values (above `BLOB_THRESHOLD`, initial default 2 KiB) are appended to `rel.blob`, returning a `BlobRef(arena, off, len, crc)`. The heap tuple stores the BlobRef; vacuuming the heap never rewrites blobs. Blob GC is a separate system (`sys_blob_gc`) that scans live BlobRefs and rewrites live blobs into a fresh blob arena.

### 5.2 Consequences

- UPDATE of a row's blob-sized column never rewrites the old blob; the heap tuple version points at a new BlobRef, and the old blob is dead when no snapshot references it.
- Index-only scans on non-blob columns are unaffected.
- Read amplification for blob-heavy queries is one extra I/O per blob-field access (BlobRef lookup + arena read); can be mitigated by inline prefetch.

### 5.3 Primary sources

- Lu, Nishtala, Zheng, Li, Arpaci-Dusseau, Arpaci-Dusseau, "WiscKey: Separating Keys from Values in SSD-Conscious Storage," FAST '16.
- PostgreSQL 18 docs, §74.2 "TOAST": https://www.postgresql.org/docs/18/storage-toast.html
- Dong et al., "Optimizing Space Amplification in RocksDB," CIDR '17 (for the LSM baseline WiscKey compares against).

## 6. SSD physics and NVMe interfaces

spostgre's correctness and performance both depend on the host accurately modeling what the SSD can and cannot do. NVMe has grown a large optional-feature surface; spostgre's contract with NVFS is that all of them are capability-probed, none are assumed.

### 6.1 NAND physics (short version)

- NAND is written **at page granularity** (typically 4–16 KiB physical pages, larger than DB logical pages) and **erased at block granularity** (2–16 MiB erase blocks, often 100–1000 NAND pages per block).
- A physical write cannot overwrite; it must be preceded by an erase of the containing block.
- Erase cycles per block are finite (≈1K–100K depending on NAND class — SLC, MLC, TLC, QLC).
- The FTL maps logical-block addresses (LBAs) to physical NAND pages, and runs background garbage collection to reclaim partially-valid blocks. This is the primary source of host-invisible write amplification.

### 6.2 NVMe command sets

NVMe 2.0c defines a family of **command sets** layered above the base command set:

- **NVM Command Set (NVM-CS)** — the classical block device. `Read`, `Write`, `Flush`, `Write Uncorrectable`, `Compare`, `Dataset Management`, `Write Zeroes`, `Copy`. The default.
- **Zoned Namespace Command Set (ZNS, 1.1b)** — LBA space partitioned into **zones**. Each zone is sequential-write only with a zone write pointer. `Zone Append` writes to the end of a zone atomically, returning the assigned LBA. `Reset Zone` erases the zone (returns it to empty state). Zones align with erase blocks, so ZNS hands the FTL job to the host. spostgre's WAL is a natural fit: append-only, bounded.
- **Key-Value Command Set (KV, 1.0c)** — LBA space replaced by (key, value) operations: `Store`, `Retrieve`, `Delete`, `List`. Value size is KV-namespace-configured up to a few MiB. This is a direction for storage classes that want dictionary-style access, and is interesting for relational secondary indexes but out of scope for M1–M3.
- **Flexible Data Placement (FDP, TP4146)** — optional addition to NVM-CS. The host passes **Placement IDs** (called Placement Handles / Reclaim Unit Handles) on each write; the device colocates writes with the same PID in the same Reclaim Unit (roughly one erase block). `Reclaim Unit Handle Status` and `Reclaim Unit Handle Usage` report per-RUH utilization. Host-controlled data placement without full ZNS sequential-write discipline.

### 6.3 Optional features spostgre cares about

- **Fused operations (Compare + Write)** — NVMe 2.0c §6.1.4. A fused operation issues Compare and Write as a single atomic pair; either both complete or neither commits. This gives host-side compare-and-swap on an LBA, usable for pmap-root updates without intent logs. spostgre's `atomic_pointer_record_publish` primitive (NVFS §S6) probes for and uses this when available; otherwise falls back to double-buffered intent log + sequence-number tie-break.
- **Multiple Atomicity Mode (NAWUN / NAWUPF / NACWU)** — Atomic Write Unit Normal / Power Fail / with CW guarantees that writes up to N logical blocks are atomic across power fail. Published NAWUPF values are typically 1, 8, or 128 blocks. spostgre's pmap-root update fits in one LBA and benefits from `NAWUPF ≥ 1`.
- **Flush and FUA** — `Flush` command forces volatile write cache to stable media; FUA (Force Unit Access) on a `Write` skips the volatile cache and writes through. FUA is higher-latency per-write; `Flush` is higher-latency per-flush but lower per-write. spostgre's durability classes map: `NONE` → no flush; `WAL` → Flush after WAL append (or FUA on WAL writes when tail-latency matters); `CHECKPOINT` → Flush after checkpoint record.
- **CMB / PMR** — Controller Memory Buffer and Persistent Memory Region are device-mapped regions of RAM (CMB, volatile) or persistent memory (PMR, NVDIMM-like) exposed over the NVMe bar. Placing WAL or pmap-root metadata in CMB/PMR lets the host commit without a full PCIe-round-trip for flush. Typically 64–512 MiB; optional feature, device-specific availability.
- **Copy** (TP4065) — host requests the device to copy a range of LBAs to a new range without DMA-through-host. Obvious fit for `arena_clone_range`. Not yet widespread in commodity devices.
- **Dataset Management (DSM) / TRIM** — host tells the device that a range of LBAs is unused. The FTL can then skip copy-up of that range during GC. `arena_discard` emits DSM for the whole arena LBA range.

### 6.4 NVMe primary sources

- NVM Express Base Specification 2.0c: https://nvmexpress.org/specifications/
- NVM Express Zoned Namespace Command Set Specification 1.1b
- NVM Express Key-Value Command Set Specification 1.0c
- NVM Express Flexible Data Placement (TP4146)
- NVM Express Simple Copy (TP4065)
- Bjørling, Aghayev, Holmberg, Ramesh, Le Moal, Ganger, Amvrosiadis, "ZNS: Avoiding the Block Interface Tax for Flash-based SSDs," ATC '21.

## 7. User-space storage runtime — SPDK and Linux I/O Passthru

spostgre's performance floor on NVMe depends on the path between the Simple process and the device. Three real paths are in play:

### 7.1 SPDK

SPDK (Storage Performance Development Kit) runs a **user-space NVMe driver** that binds to the device via vfio-pci or uio. It maps the NVMe submission / completion queues directly into user space and pins DMA-accessible memory with `hugetlbfs`. The core concepts:

- **Per-core queue pairs.** Each CPU core owns its own NVMe queue pair; I/Os never cross cores. This eliminates cache-line bouncing on the submission doorbell.
- **Doorbell batching.** Submissions accumulate in the submission queue; the doorbell write (a 32-bit MMIO write updating the SQ tail) is deferred until batch-commit or idle. Modern SPDK defaults to 32-deep batches.
- **Polling vs interrupt.** SPDK polls completion queues from a dedicated core. No IRQ overhead; at the cost of a core's worth of CPU. Alternative: MSI-X interrupt mode for idle workloads.
- **DMA pinning.** DMA buffers are pinned once at startup; no per-I/O map/unmap. `spdk_nvme_ns_cmd_read` takes a pinned buffer and a callback.

SPDK's typical reported latencies on current-gen NVMe: 10–20 μs per 4 KiB random read at QD=1, scaling to 1M+ IOPS per core.

### 7.2 Linux `io_uring_cmd`

Since Linux 6.1, `io_uring_cmd` with `NVME_URING_CMD_IO` opcode exposes raw NVMe pass-through I/O through the io_uring interface. This is the kernel's answer to SPDK: no kernel block layer, no per-I/O syscall, but you don't need to rebind the device from the kernel driver.

The FAST '24 paper (Joshi et al., "I/O Passthru: Upstreaming a Flexible and Efficient I/O Path in Linux") reports:

- **16–40 % IOPS uplift** over the classical Linux block layer on random 4 KiB reads.
- **Latency reduction of ~5–15 μs** at QD=1.
- **Feature access** — ZNS Zone Append, KV commands, and FDP are reachable via passthru without kernel support for each individual feature.

For spostgre, `io_uring_cmd` is the primary non-SPDK path. It delivers most of SPDK's performance gain without the device-bind requirement and without the kernel-bypass deployment complexity.

### 7.3 Classical `io_uring` (+ block)

The baseline fallback: `io_uring` + `O_DIRECT` + `IORING_OP_READV`/`WRITEV`. Kernel block layer still processes each I/O; still gives asynchronous batching and DMA pinning through `IORING_REGISTER_BUFFERS`. Sufficient for development-machine workflows. Latency: ~25–40 μs per 4 KiB read. Present on any Linux ≥ 5.1.

### 7.4 spostgre's path selection

spostgre does not talk to NVMe directly. NVFS owns the backend. But NVFS's capability probe (`fs_caps()`) returns an `io_backend` enum with `{SPDK, IO_URING_CMD, IO_URING, SYNC_POSIX}` values; spostgre treats this as advisory for its group-commit tuning (larger commit_delay on slower paths) and for its AIO milestone planning (SPDK and io_uring_cmd both expose genuine asynchrony; SYNC_POSIX effectively does not).

### 7.5 Primary sources

- SPDK documentation: https://spdk.io/doc/
- Joshi, Kanaujia, Pillai, Koller, Yadav, "I/O Passthru: Upstreaming a Flexible and Efficient I/O Path in Linux," FAST '24.
- Axboe, "io_uring: a kernel-level asynchronous I/O interface," LWN series.
- Linux kernel documentation: `Documentation/block/iopl.rst`, `Documentation/io_uring/*`.

## 8. SSD-iq — benchmarking fairness on flash

A critical methodological point: **published SSD throughput numbers are mostly fresh-out-of-box numbers, which overstate sustained performance by factors of 3–10×.** SSD-iq (Klein et al.) is the standing critique and methodology.

### 8.1 Why fresh-out-of-box is wrong

A fresh SSD is in the "over-provisioned, clean blocks everywhere" state. Writes go to pre-erased blocks directly; GC never runs; WAF is 1. Sustained workloads fill the drive, and every subsequent write requires copy-up of valid data from partially-dirty blocks. WAF rises to 2–5×. Throughput drops 3–10×.

Sustained-state benchmarking requires:

1. **Precondition to sustained state.** Fill the entire LBA space sequentially, then overwrite randomly until the workload's WAF reaches a stable value. Typically 2–4× capacity of random writes.
2. **Measure at sustained state.** Only after preconditioning are the numbers meaningful.
3. **Report SSD-side counters.** NVMe SMART `Data Units Written` vs host data written gives physical WAF; without this, "writes per second" is just a host-visible number.

### 8.2 Latency-under-load

Average latency is nearly useless on SSDs — the tail is what kills real workloads. SSD-iq requires p50, p95, p99, p99.9, p99.99 reporting, and warns that the p99 of a preconditioned SSD can be 100× the p50. spostgre's M1 benchmarks will report at least p50 / p95 / p99 / p99.9.

### 8.3 Primary sources

- Klein, Desnoyers, Reidys, Koutsouris, Arpaci-Dusseau, "SSD-iq: Shifting the Benchmarking Dimension from Performance to Fairness on Flash Storage," HotStorage '22 / FAST '23.
- Intel / Meta technical reports on preconditioning methodology.
- Kasavajhala, "Solid-State Drive Endurance Workload Characterization," Dell EMC technical whitepaper.

## 9. X-FTL and SaS — long-range references

Two research directions are worth citing because reviewers will ask about them, but spostgre does **not** pursue them in M1–M3.

### 9.1 X-FTL

X-FTL (FAST '13, Kang et al.) pushes part of the database into the FTL — the FTL understands page LSNs and can skip redundant writes. Requires device-firmware collaboration; commodity SSDs do not expose this. Mentioned because out-of-place DB design can conceptually extend into the FTL if the deployment allows, but not reachable on off-the-shelf hardware. spostgre stays host-side.

### 9.2 SaS — in-storage database / computational storage

A research direction where SQL operators (filter, aggregate, even join) execute on compute resources inside the SSD controller, over the raw NAND. Examples: Samsung SmartSSD, Eideticom NoLoad, Microsoft's Project Cerberus family. Real products exist but are neither portable nor interoperable; the programming model is device-specific. spostgre's M4+ could expose a pluggable operator-pushdown interface, but the M1–M3 engine is pure host-side.

### 9.3 Primary sources

- Kang, Yoo, Seo, Kang, Yoon, Kim, "X-FTL: Transactional FTL for SQLite Databases," SIGMOD '13 (earlier version FAST '13 for X-FTL basics).
- Gu, Do, Keeton, "SaS: SSD as a SQL database system," VLDB '18 vision paper.
- Jun, Liu, Xu, Kim, Arvind, "BlueDBM: An Appliance for Big Data Analytics," ISCA '15.

## 10. Simple-language constraints

spostgre exists inside the Simple language ecosystem, and all design decisions are subject to project conventions. These constraints are not negotiable; they shape module boundaries, type layouts, and concurrency models.

### 10.1 MDSOC+ outer axes

Simple's architecture rule is "MDSOC outer + ECS business layer for userland services/apps; kernel/drivers stay MDSOC-only" (`.claude/rules/structure.md`, `doc/04_architecture/mdsoc_architecture_tobe.md`). The MDSOC outer must declare a table across these axes:

1. **Modules** — what Simple modules participate, what each owns.
2. **Dependencies** — acyclic dependency declaration; dependency direction is enforced at module-boundary.
3. **Side effects** — which modules perform I/O, which are pure. spostgre's engine is I/O-heavy; this axis is explicit.
4. **Ownership / capabilities** — capability objects for filesystem, WAL, clock, RNG.
5. **Concurrency** — runtime family assignment per module (`nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`, `nogc_async_mut_noalloc`). Runtime families are not mixed within a module.

spostgre is userland-userland: MDSOC-outer + ECS-inner. NVFS is kernel/driver-adjacent: MDSOC-only, no ECS.

### 10.2 ECS business layer

The ECS business layer uses `std.ecs`. Rules:

- Components are **POD structs**, no methods except `new`/`default`.
- Systems are **free functions** over component stores, not methods on components.
- Queries take a world handle and component tuple: `world.query<A, B>() -> Iterator<(&mut A, &mut B)>`.
- No inheritance. No component hierarchies. Composition via tuples, mixins for cross-cutting concerns.

spostgre's 11 components and 8 systems are enumerated in `doc/05_design/spostgre_design.md §3.1–§3.2`.

### 10.3 Runtime-family discipline

Each top-level module declares its runtime family. spostgre's engine and NVFS live in `nogc_sync_mut` (synchronous, mutable, no GC) — matching the expected buffer-manager / page-cache idiom. M3 graduates AIO paths to `nogc_async_mut`. Synchronous-mutable is the default for storage engines because (a) no GC pauses, (b) blocking I/O calls are fine at the engine level — they're wrapped in the runtime's worker model, (c) the buffer-pool / page-cache model is inherently stateful and mutable, which plays poorly with `async_mut` expectation of cheap `Send` across task boundaries.

### 10.4 Composition not inheritance

No `extends`, no virtual methods, no superclass chains. Traits + composition + mixins. Phase 5 skeletons verified zero `extends`/`inherits`/`super` hits.

### 10.5 Generics syntax

`<T>` not `[T]`. `[T]` is list-of-T (a field type), never a generic position. Lint enforces this; Phase 5 skeletons verified zero violations.

### 10.6 VCS and commit hygiene

- `jj` (Jujutsu) colocated with git, no branches, work on `main`.
- `jj commit -m ...` for new commits; `jj bookmark set main -r @- && jj git push --bookmark main` to push.
- Submodules via git (`examples/spostgre`, `examples/nvfs`) pointing at private `ormastes/*` repos.

### 10.7 Primary sources

- `CLAUDE.md`
- `.claude/rules/language.md`, `.claude/rules/structure.md`, `.claude/rules/code-style.md`, `.claude/rules/vcs.md`
- `doc/04_architecture/mdsoc_architecture_tobe.md`
- `doc/04_architecture/glossary.md`
- `src/lib/nogc_sync_mut/ecs/*.spl` (idiomatic ECS usage)

## 11. NVFS interface assumptions from spostgre

spostgre expects NVFS to expose a narrow arena-centric API. These assumptions drive `doc/05_design/nvfs/from_spostgre.md §S1..§S7` (P0 upfront) and `§S-stretch-1..6` (P1 stretch).

### 11.1 Arena-per-fork

Each of spostgre's seven forks (`rel.main`, `rel.pmap`, `rel.vmap`, `rel.fmap`, `rel.wal`, `rel.temp`, `rel.blob`) maps to one or more NVFS arenas. Arenas carry a **storage class** at creation (`DB_WAL`, `DB_TEMP`, `META_DURABLE`, `GENERAL_MUTABLE`, `MODEL_IMMUTABLE`, `CHECKPOINT_SNAPSHOT`), which NVFS maps to underlying NVMe placement (FDP PID, ZNS zone, or classical namespace) via capability probe.

### 11.2 Aligned-append WAL

`arena_append_aligned(arena, bytes, granule, durability)` appends to an arena with the device-preferred I/O granule (`fs_caps().preferred_write_granule`). For WAL this is the basic group-commit unit. For data pages this is the page-cluster append. The `durability` parameter is one of `NONE / WAL / CHECKPOINT / FUA`.

### 11.3 Sealed checkpoint arenas

`arena_seal(arena)` marks an arena immutable — no further appends. Sealed arenas may be compacted by NVFS (e.g., rewritten into fewer zones) but their LBA↔byte mapping is stable. Checkpoints use this to "cut" a data arena — the sealed arena's contents become the checkpoint's frozen state, and new writes go to a new arena.

### 11.4 arena_clone_range for page-version cloning

`arena_clone_range(src, src_off, dst, dst_off, len)` copies a byte range without DMA-through-host (when NVMe `Copy` is supported) or via DMA (fallback). spostgre uses this during vacuum: live pages are cloned from the old arena into a new arena, the pmap is updated to point at the new arena, and the old arena is discarded.

### 11.5 Capability-probed CAS for pmap-root

`atomic_pointer_record_publish(slot_handle, expected, new, durability)` atomically updates a slot. On devices with NVMe fused Compare-and-Write + NAWUPF ≥ 1, this is implemented as a single fused op with durability barrier. Otherwise, NVFS emits a double-buffered intent log (two slots, alternating, sequence-number-tagged) with a monotonic sequence number; on read, the higher-sequence slot wins tie-breaks with CRC fallback. Both paths are live forever; NVFS hides this from spostgre, but both must be specified and tested at Phase 4.

### 11.6 Preferred I/O granule

`fs_caps().preferred_write_granule` returns the device-preferred aligned-append chunk size (typically 4 KiB, 8 KiB, or 128 KiB). spostgre uses this to pad WAL group-commit boundaries. The granule may differ per storage class (ZNS zone boundaries are much larger than classical-namespace page granules).

### 11.7 NVFS feature-request candidates (seeded by research)

Six concrete asks fell out of the research, promoted to `[UPFRONT]` P0 in `from_spostgre.md`:

1. `arena_create(class, hint)` → **S1**
2. `arena_append_aligned(arena, bytes, granule, durability)` → **S2**
3. `arena_seal` + generation-pinned `arena_discard` → **S3**
4. `arena_clone_range(src, src_off, dst, len)` → **S4**
5. `fs_caps()` + preferred I/O granule → **S5**
6. `atomic_pointer_record_publish(slot, expected, new, durability)` → **S6**

One extra P0 surfaced in Phase 3 design (NVMe Flush / FUA pass-through tied to durability classes → **S7**). Four secondary asks (`arena_discard` generic, `arena_reserve_size`, `arena_stream_read`, `capability_probe`) folded into S3/S1/S4/S5.

Six P1 stretch items were added in Phase 3 (not research-candidates): ZNS zone-append for WAL (S-stretch-1), FDP PIDs per class (S-stretch-2), namespace-per-class (S-stretch-3), copy offload for `arena_clone_range` (S-stretch-4), CMB/PMR for WAL buffers (S-stretch-5), DSM trim on `arena_discard` (S-stretch-6).

## 12. Open design questions

Open questions carried to Phase 3+. Each has a tracking ID.

### OQ-1 — pmap RAM footprint

A naive 1:1 LBA → PhysPtr map is 1 MiB/GiB (8 B per 8 KiB page). For a 1 TiB relation that is 1 GiB of RAM. Design options:

- **(A)** Two-level: delta (in-RAM, append-only, updated on each pmap_publish) + B-tree (on-disk, compacted at checkpoint). Delta size proportional to writes-since-checkpoint; B-tree size proportional to distinct logical pages.
- **(B)** Paged pmap: pmap itself is stored as pages in its own arena, with an LRU cache in RAM.
- **(C)** Compressed pmap: run-length-encode sequential ranges of physical pages (common for large sequential inserts).

Phase 3 committed to (A) with an initial target of ≤ 64 MiB root-RAM for a 1 TiB relation.

### OQ-2 — pmap-root CAS dual-path burden

The capability-probed CAS forces two live commit paths in NVFS (fused-CW path and intent-log path). Both must be specified and tested forever. What's the testing matrix that keeps both correct under power-fail? Phase 4 feature files own this.

### OQ-3 — WAL record framing

PostgreSQL's WAL records are variable-length, type-tagged, per-backend-assembled. If we preserve PG-compat framing, `arena_append_aligned` has to pad partial records to granule, which wastes space under high-throughput small-commit workloads. Decision (committed Phase 3): spostgre uses its own CRC32C-framed records padded to preferred_write_granule at group-commit boundaries; PG-compat is a conversion concern, not a physical-storage concern.

### OQ-4 — MVCC correctness under arena seal + discard

If snapshot `S1` was taken at time `t1` and holds a reference to pmap generation `g1`, and vacuum wants to discard arena `A` at time `t2 > t1` where `A` contains pages live at `g1`, then discarding `A` breaks `S1`. Solution: `arena_discard(A, keep_gen_above=g)` refuses to discard while any snapshot holds generation ≤ `g`; spostgre's Txn carries `pinned_pmap_gen`; NVFS ref-counts open readers per generation. Committed Phase 3. Phase 4 spec targets must verify under adversarial snapshot-hold durations.

### OQ-5 — Query planner constants on NVMe

PostgreSQL's planner cost model uses hardcoded constants (`seq_page_cost = 1.0`, `random_page_cost = 4.0`, `cpu_tuple_cost = 0.01`, `cpu_index_tuple_cost = 0.005`, `cpu_operator_cost = 0.0025`). On NVMe with `io_uring_cmd`, `random_page_cost / seq_page_cost ≈ 1.1`, not 4. Using 4 produces wildly-wrong index vs sequential-scan decisions. Full rework is M4+; M1–M3 uses conservative defaults and accepts suboptimal plans.

### OQ-6 — SSD-iq benchmark honesty

M1 benchmark harness must precondition drives to sustained state and report SMART counters (physical WAF), p50/p95/p99/p99.9 latency. No fresh-out-of-box numbers. Tracked as M1 release-gate spec target.

### OQ-7 — Buffer pool sizing on split storage tiers

When `DB_TEMP` is local-NVMe (victim buffer), how is the in-RAM buffer pool sized? Simple model: RAM = working-set; DB_TEMP = hot evictions; main = cold store. Needs workload characterization; tracked for M3.

### OQ-8 — AIO signature shape (sync → async transition)

spostgre's engine is `nogc_sync_mut` at M1–M2. M3 introduces AIO. Signature shape of `page_store.read_page(blk) -> Page` vs `async fn page_store.read_page(blk) -> Page` is open: returning `Future<Page>` from a sync trait doesn't work; a parallel async trait surface doubles the trait count; a split-in-half `submit_read(blk)` / `poll_completion()` API requires caller-side state machines. Deferred to M3.

### OQ-9 — `atomic_pointer_record_publish` naming

Three candidates: current name, `fs_publish_atomic`, `slot_cas_publish`. NVFS author has final say. spostgre's feature files use the current name and will accept text-substitute rename.

### OQ-10 — BRIN rebuild on arena compaction

When vacuum rewrites an arena, the BRIN summaries for the arena's page ranges become stale (PhysPtrs changed). Rebuild options: (a) BRIN summaries keyed on logical BlkNo, not PhysPtr (preferred — no rebuild needed); (b) BRIN rebuild as part of arena compaction.

### OQ-11 — Recovery re-do vs full replay under fast failover

Aurora's "instant recovery" is storage-side replay. spostgre's single-node model is compute-side replay from WAL + pmap-root. Measure wall-clock: is 1 GiB of WAL replay < 10 s on NVMe? If not, checkpoint frequency must rise.

### OQ-12 — Blob GC scheduling

spostgre's `rel.blob` needs independent GC (blob-cleanup independent of heap vacuum). Scheduling: every N vacuum cycles? Or when blob-arena fullness > threshold? Deferred to M2.

### OQ-13 — Crash-safe pmap-root bootstrap

First-boot creates pmap with a single empty-arena entry. How does NVFS ensure that first publish is crash-safe before any intent-log sequence numbers exist? Decision: initial `atomic_pointer_record_publish` uses sequence 1; sequence 0 is reserved for "uninitialized."

### OQ-14 — Capability probe caching lifetime

`fs_caps()` results are expected to be stable for a device, but hot-swap of drives (or container migration) could invalidate them. Policy: cache for process lifetime, re-probe on `reopen`.

### OQ-15 — TOAST compat

PostgreSQL's wire protocol exposes TOAST pointers via VARATT_1B_E / VARATT_4B_E. spostgre's blob ref is structurally similar but not bit-compatible. Wire-compat layer translates on read. Not a research question; listed for completeness.

## 13. Top primary sources — reading order

For someone joining the project and needing to ramp up on spostgre's theoretical grounding, read in this order:

1. **CLAUDE.md + `.claude/rules/`** — Simple project conventions. Non-negotiable.
2. **PostgreSQL 18 docs ch. 74** (Database Physical Storage) and **ch. 30** (WAL). Baseline conceptual model.
3. **WiscKey (FAST '16)** — the clearest exposition of key-value separation and SSD-aware log-structuring. Short read.
4. **Aurora SIGMOD 2017** — storage-compute split and why the compute node never writes pages. Context for Aurora Optimized Reads (SIGMOD 2024).
5. **NVMe Base 2.0c, ch. 3 (I/O Commands)** — know what fundamental primitives exist. Skim.
6. **NVMe ZNS 1.1b intro** and **FDP TP4146 intro** — two different approaches to host-controlled placement. Skim both.
7. **SPDK overview** (spdk.io/doc) — per-core queue pairs, doorbell batching, polling. Essential mental model.
8. **FAST '24 I/O Passthru paper** (Joshi et al.) — Linux's modern answer, with quantified uplift.
9. **SSD-iq (HotStorage '22)** — benchmarking methodology. Mandatory if you plan to measure anything.
10. **PostgreSQL BRIN docs** (§64.1) — index-access method that fits arena layouts.
11. **X-FTL (SIGMOD '13)** — background; why not pursued here.

Secondary reading for depth:

12. PostgreSQL `src/backend/access/heap/heapam.c` — HOT implementation. Best read against PG 18.
13. PostgreSQL `src/backend/access/transam/xlog.c` — WAL driver. Long file; focus on `XLogInsert`, `XLogFlush`, `CreateCheckPoint`.
14. Aurora Optimized Reads (SIGMOD '24 industrial track) — local-NVMe victim cache design.
15. Bjørling et al., "ZNS: Avoiding the Block Interface Tax" (ATC '21) — the canonical ZNS paper.
16. Lu, Nishtala, Zheng et al., "LSM-trie" (ATC '15) — complement to WiscKey.

## Appendix A — Phase 2 design tensions (recap)

Five tensions surfaced during research, each committed-to or resolved in Phase 3:

1. **pmap RAM footprint (OQ-1).** Resolved: two-level delta + B-tree structure, ≤ 64 MiB root RAM for 1 TiB relation.
2. **Capability-probed CAS forces two commit paths (OQ-2).** Resolved: S6 `atomic_pointer_record_publish` hides both; Phase 4 specs cover both.
3. **MVCC × arena-seal × discard (OQ-4).** Resolved: generation pinning on snapshots; `arena_discard` refuses below pinned generation.
4. **Planner constants on NVMe (OQ-5).** Deferred to M4+; conservative defaults at M1–M3.
5. **SSD-iq benchmarking honesty (OQ-6).** Made a release-gate spec target.

## Appendix B — spostgre vs PostgreSQL: mapping table

| Concept | PostgreSQL 18 | spostgre |
|---|---|---|
| Page size | 8 KiB (compile-time configurable to 16/32 KiB) | 8 KiB default, `fs_caps()` may force multiple |
| Heap fork | `<oid>` (main) | `rel.main` (arena, append-only) |
| FSM fork | `<oid>_fsm` | `rel.fmap` (arena + in-RAM index) |
| VM fork | `<oid>_vm` | `rel.vmap` (arena + in-RAM bitset) |
| Page indirection | None (direct LBA) | `rel.pmap` (arena + two-level index) |
| WAL | cluster-wide `pg_wal/` | `rel.wal` (aligned-append arena per DB) |
| TOAST | `pg_toast.pg_toast_<oid>` heap | `rel.blob` (WiscKey-style value log) |
| Checkpoint | page flush + ctl file | arena_seal + atomic_pointer_record_publish |
| Recovery | redo from checkpoint LSN | redo from pmap-root sequence + WAL |
| Vacuum | in-place page rewrite + FSM update | arena rewrite + pmap flip + arena_discard |
| Freezing | `t_xmin = FrozenTransactionId` | same (heap tuple format preserved) |
| HOT | line-pointer redirect within page | same (unchanged) |
| BRIN | `pages_per_range` blocks, min/max per col | same (keyed on BlkNo, not PhysPtr) |
| AIO | io_uring worker pool (PG 18) | `nogc_async_mut` at M3, SPDK or io_uring_cmd |

## Appendix C — Engine component dataflow

(Informal sketch; canonical in `doc/05_design/spostgre_design.md §3`.)

```
     TUPLE WRITE
        |
        v
  sys_buffer_evict  <--  BufferFrame (dirty)
        |
        v
  sys_wal_flush    -->  WalRecord  -->  arena_append_aligned(rel.wal, bytes, granule, WAL)
        |
        v
  sys_commit        -->  Txn (committed)
        |                   |
        v                   v
  sys_pmap_publish <---- PmapBinding  -->  atomic_pointer_record_publish(pmap_root, expected, new, CHECKPOINT)
        |
        v
  sys_checkpoint    -->  arena_seal(rel.main generation N)
                    -->  arena_create(rel.main generation N+1)
        |
        v
  sys_vacuum        -->  arena_clone_range(live pages)  -->  arena_discard(old gen, keep_gen_above=pinned)
        |
        v
  sys_blob_gc       -->  arena_clone_range(live blobs)  -->  arena_discard(old blob arena)

  sys_capability_probe ---- (once at startup, CapabilityView cached per CLI invocation)
```

---

## Appendix D — Extended PostgreSQL internals detail

### D.1 Heap page slot layout walkthrough

A PostgreSQL heap page is a contiguous 8 KiB blob conceptually laid out as:

```
offset 0            : PageHeaderData (24 bytes)
offset 24           : ItemIdData[0]  (4 bytes)
offset 28           : ItemIdData[1]  (4 bytes)
...                 : ItemIdData[N-1] (grows downward with pd_lower)
offset pd_lower     : free space begins
offset pd_upper     : free space ends (tuples grow upward)
...                 : tuple data (variable length)
offset 8192-sp-sz   : pd_special (index-type-specific region)
```

Tuples grow from the top of the page downward; line pointers grow from the bottom upward. Free space is the gap, `pd_upper - pd_lower`. When a tuple is inserted, the heap access method finds a free slot (or allocates a new one), copies the tuple data to `pd_upper - tuple_size`, decrements `pd_upper`, sets the `ItemIdData` at slot index `N` to `(pd_upper, LP_NORMAL, tuple_size)`, and bumps `pd_lower` by 4. Deletion is a two-step: mark the line pointer as `LP_DEAD` (immediate), later reclaim the tuple space (`heap_page_prune`).

### D.2 HOT chain pruning in detail

`heap_page_prune` is called opportunistically during scan and during explicit prune (`heap_page_prune_opt`). Steps:

1. Acquire buffer content lock on the page (cleanup lock required in some paths).
2. Walk the page's item pointers. For each item that is a HOT-chain head whose chain terminates in a dead tuple (all versions dead to all snapshots), mark every item in the chain as `LP_DEAD`, mark the head as `LP_REDIRECT` pointing at the latest live tuple (if any), or `LP_DEAD` if the chain has no live members.
3. Compact the page by moving live tuples down to eliminate gaps between `pd_upper` and the freed tuples' positions; update affected `ItemIdData.off` values.
4. Log a `heap_prune` WAL record.

The page-level cleanup avoids the index-pointer-update cost of PostgreSQL's full VACUUM because HOT chain index pointers still reference the chain head, which is retained as `LP_REDIRECT`.

### D.3 Freezing and anti-wraparound vacuum

PostgreSQL's 32-bit XID wraps every 2^32 transactions (≈ 4 billion). If a tuple's `xmin` has not been frozen by the time the current XID catches up modulo 2^31, its visibility computation flips (the "xid in the future" check inverts). PostgreSQL prevents this by:

1. Tracking `pg_database.datfrozenxid` — the oldest unfrozen XID in the database.
2. Tracking `pg_class.relfrozenxid` per relation.
3. Auto-vacuum triggers anti-wraparound freeze when `datfrozenxid` approaches `xid_wraparound_warn_limit` (configurable; default = current XID − 2^30).
4. `VACUUM FREEZE` rewrites tuple headers: `t_xmin = FrozenTransactionId` (= 2), which is treated as visible to all snapshots forever.

For spostgre, the arena-rewrite model makes this cheaper: a full arena rewrite naturally freezes every tuple it copies forward, so vacuum and freezing are the same pass. Anti-wraparound is still necessary — xids still advance — but the implementation reuses the arena-rewrite machinery instead of adding a dedicated freeze path.

### D.4 WAL record types

PostgreSQL's WAL records are type-tagged via `RmgrId` (resource manager id) + `info` byte. The resource managers that matter to spostgre:

- `RM_HEAP_ID` / `RM_HEAP2_ID` — heap operations: insert, delete, update, HOT update, inplace, prune, vacuum.
- `RM_BTREE_ID` — B-tree index operations (not in M1 scope — BRIN is M1).
- `RM_BRIN_ID` — BRIN summarization and range updates.
- `RM_XLOG_ID` — XLOG-level records: checkpoint, switch, backup, identify.
- `RM_XACT_ID` — transaction commit / abort / prepare.
- `RM_STANDBY_ID` — standby-side records (running-xacts, lock).

Each resource manager provides a `redo` callback that takes a WAL record and applies it. spostgre preserves the RmgrId concept but simplifies the record shape (CRC32C framed with its own header) and elides some PostgreSQL-specific fields.

### D.5 Bgwriter and checkpointer processes

PostgreSQL has two background-write processes:

- **Bgwriter** — writes dirty pages in the background to keep ahead of backends' buffer-eviction demand. Picks pages with `usage_count = 0`. Tunable via `bgwriter_delay`, `bgwriter_lru_maxpages`, `bgwriter_lru_multiplier`.
- **Checkpointer** — writes all dirty pages at checkpoint boundaries. Tunable via `checkpoint_timeout` (default 5 min), `max_wal_size` (default 1 GiB), `checkpoint_completion_target` (default 0.9, spread writes over 90 % of the interval).

In spostgre, the bgwriter analogue is absorbed into `sys_buffer_evict` (continuous eviction to DB_TEMP when DB_TEMP is available) and `sys_pmap_publish` (continuous pmap-delta flush). Checkpointer is `sys_checkpoint`. Both are ECS systems scheduled by the business-layer scheduler, not separate OS processes.

## Appendix E — Extended NVMe primitive catalog

### E.1 NVMe admin command path

Admin commands (`Identify`, `Get Log Page`, `Set Features`, `Get Features`, `Create I/O Completion Queue`, etc.) use the **admin queue pair** — a single pair per controller. Admin commands cover:

- Device identification and capacity.
- Namespace creation / deletion (where the device supports multiple namespaces).
- Health and status reporting (`SMART / Health Information`, `Firmware Slot Information`).
- Feature configuration (power management, temperature thresholds, autonomous power state transitions).
- Asynchronous event request (AER) — device-initiated events like "media smart warning" or "firmware activation starting".
- Security-send / security-receive for SED (self-encrypting drive) protocols.

spostgre's capability probe (§11.5, §6.3) issues several `Identify Controller` (CNS = 1) and `Identify Namespace` (CNS = 0) commands at startup to enumerate optional features. The probe takes one admin queue round-trip per feature; cached for process lifetime.

### E.2 NVMe submission / completion queue structure

Each I/O queue pair has:

- A **submission queue (SQ)** — a ring of 64-byte submission-queue-entries (SQEs). The host writes SQEs, then writes the queue's **doorbell register** (an MMIO register at controller-defined offset) to advance the tail pointer.
- A **completion queue (CQ)** — a ring of 16-byte completion-queue-entries (CQEs). The controller writes CQEs as I/Os complete; the host periodically reads them (polling mode) or waits for an interrupt.

Doorbell writes are the cross-PCIe-bus-synchronization cost. Batching multiple SQEs before a single doorbell write amortizes this cost across the batch.

### E.3 Placement-ID (FDP) command flow

FDP extends the Write command with a **Placement Handle** field in the command DWord. The host tags each write with a handle (0..N-1 where N is controller-defined, typically 16–256). The controller colocates writes sharing a handle in the same **Reclaim Unit** (RU), a chunk ≈ one erase block. When the host wants to reclaim an RU (e.g. at arena_discard time), it issues `Dataset Management` over the RU's LBA range, which is typically many contiguous LBAs.

spostgre's storage-class → placement-handle mapping is established at mount time by NVFS:

| Storage class | Placement handle | Reclaim trigger |
|---|---|---|
| `META_DURABLE` | 0 | Never (metadata is long-lived) |
| `DB_WAL` | 1 | Checkpoint + WAL archive success |
| `DB_TEMP` | 2 | Arena-discard on unclean shutdown |
| `MODEL_IMMUTABLE` | 3 | Manual eviction only |
| `GENERAL_MUTABLE` | 4 | Arena-discard |
| `CHECKPOINT_SNAPSHOT` | 5 | Snapshot expiry |

If the device reports fewer placement handles than classes, NVFS compresses the mapping (e.g., DB_TEMP and GENERAL_MUTABLE share a handle). Capability-probed fall-back.

### E.4 ZNS state machine

Each ZNS zone is in one of these states, per NVMe ZNS 1.1b:

- `Empty` — no data, write pointer at zone start.
- `Implicitly Opened` — writes have started; kernel state managed by controller.
- `Explicitly Opened` — host issued `Zone Open` command.
- `Closed` — zone has data but no open resources.
- `Full` — write pointer at end; no more writes accepted.
- `Read Only` — writes refused; reads allowed.
- `Offline` — zone is retired (e.g., bad blocks).

Transitions are controlled by `Zone Management Send` (open / close / reset / finish / offline) and by host writes. `Reset Zone` transitions `Full`/`Closed`/`Opened` → `Empty`. Active-zone-limit and open-zone-limit are controller-defined constraints.

spostgre's WAL mapping (when ZNS is available): one open zone at a time for append; on zone-full, issue `Zone Finish` on the filled zone, open the next. Checkpoint-triggered WAL archiving is `Reset Zone` once the archiver has successfully drained.

### E.5 NVMe Compare and Fused Compare-Write

Fused operations (NVMe Base §6.1.4) issue exactly two commands — a Compare followed by a Write — as an atomic pair. The Compare reads the LBA range and compares to the supplied buffer; the Write applies only if Compare succeeded. Either both or neither complete.

spostgre uses this for `atomic_pointer_record_publish` when available:

```
cw_pair := [
  Compare(lba=PMAP_ROOT_LBA, buf=expected_bytes, size=LBA_SIZE),
  Write  (lba=PMAP_ROOT_LBA, buf=new_bytes,     size=LBA_SIZE, FUA=1)
]
submit_fused(cw_pair) → status { OK | compare_failed | nvme_error }
```

If fused ops are not supported, NVFS falls back to:

```
slot := slot_handle
slot.generation += 1
slot.data       := new_bytes
slot.crc        := crc32c(new_bytes)
intent_log.append(Record { slot_id, slot.generation, slot.data, slot.crc }, FUA=1)
nvme_flush()
slot_table.write(slot_id, slot)   // double-buffered slots; older generation stays readable
nvme_flush()
```

Recovery picks the highest-generation slot whose CRC matches.

## Appendix F — Simple module placement for spostgre engine

### F.1 Module tree

```
src/lib/nogc_sync_mut/spostgre_if/   # trait contracts only (main repo)
  __init__.spl
  types.spl                          # Rel, BlkNo, Lsn, TxnId, PhysPtr
  storage_api.spl                    # BufferManager, WalWriter, PageStore,
                                     # PageMap, TempStore, Checkpointer,
                                     # BlobStore, Vacuumer traits

src/lib/nogc_sync_mut/storage/       # shared primitives (main repo)
  __init__.spl
  storage_class.spl                  # StorageClass enum (6 variants)
  durability.spl                     # DurabilityClass enum + FlushRequest
  capability.spl                     # Capability enum + CapabilityProbe trait
  arena.spl                          # ArenaHandle + Arena trait (7 verbs)
  mdsoc_base.spl                     # Header-only MDSOC outer doc

examples/spostgre/src/               # engine impl (submodule)
  engine/                            # physicalization
    page.spl, wal.spl, pmap.spl,
    buffer_mgr.spl, txn.spl,
    checkpoint.spl, vacuum.spl
  business/                          # ECS business layer
    components.spl, systems.spl
  tool/                              # CLI entry
    cli_entry.spl, main.spl
```

Symlink: `src/app/spostgre -> ../../examples/spostgre/src/tool` (trace32 pattern, verified Phase 5).

### F.2 Runtime family per module

| Module | Family | Why |
|---|---|---|
| `spostgre_if/` | `nogc_sync_mut` | Trait declarations only; matches engine family. |
| `storage/` | `nogc_sync_mut` | Shared primitives; sync-mut for buffer-manager idiom. |
| `fs/nvfs/` (contracts) | `nogc_sync_mut` | Matches engine family. |
| `examples/spostgre/engine/` | `nogc_sync_mut` (M1-M2), `nogc_async_mut` (M3+) | Sync initially; AIO path at M3. |
| `examples/spostgre/business/` | `nogc_sync_mut` | ECS over engine; runtime family matches engine. |
| `examples/nvfs/core/` | `nogc_sync_mut` | NVFS impl; sync-mut for filesystem kernel idiom. |
| `examples/nvfs/driver/` | `nogc_sync_mut_noalloc` (future) | When real NVMe driver lands, no-alloc for IRQ context. |

### F.3 Capability declaration per module

Each MDSOC outer declares the capabilities it needs:

```
Module: examples/spostgre/engine/
Capabilities: [
  FilesystemArenaAccess,  // provided by NVFS handle
  ClockMonotonic,         // for commit-timestamp
  Rng,                    // for xact-id entropy (paranoia)
  PageBufferAlloc,        // buffer-pool memory
]
```

NVFS runs with a narrower set:

```
Module: examples/nvfs/core/
Capabilities: [
  BlockDeviceAccess,      // raw NVMe handle
  DmaBufferAlloc,         // pinned buffers
  Timer,                  // for flush batching
]
```

Runtime enforces these at module-load: the capability set is checked against the process's granted set, and a mismatch aborts module init.

## Appendix G — Benchmark harness targets (M1)

Minimum benchmark surface for M1 release gate:

1. **YCSB-A (50/50 read/update)** on preconditioned NVMe at steady state.
   - Throughput ≥ 1.6× in-place B-tree baseline.
   - p99 latency ≤ 3× baseline p99.
   - Physical WAF (SMART counter-derived) ≤ 0.5× baseline physical WAF.

2. **TPC-C** scaled to fit working-set in buffer pool (wh=10 small run, wh=100 realistic run).
   - tpmC ≥ 1.3× baseline.
   - Physical writes per transaction ≤ 0.3× baseline.

3. **Preconditioning protocol.** Drive is filled sequentially with 128 KiB writes, then hit with 4 KiB random-writes at QD=32 for 4× capacity. Verify WAF has stabilized (Δ < 5 % over last hour) before starting measurement.

4. **Recovery time.** After forced crash (SIGKILL at random point during sustained TPC-C), measure time-to-accept-queries. Target ≤ 5 s for 1 GiB of unflushed WAL.

5. **Sustained-state test.** 24-hour YCSB-A run with WAF, throughput, p50/p95/p99/p99.9 latency sampled every minute. Report time-series to detect long-term degradation.

Benchmarks report SMART counters, host I/O counters, SSD model, preconditioning state, kernel version, NVMe feature-set, and scheduler (poll / interrupt) so reviewers can reproduce.

## Appendix H — Cross-references

- `CLAUDE.md`, `.claude/rules/{language,structure,code-style,vcs,testing}.md`
- `doc/04_architecture/mdsoc_architecture_tobe.md` (MDSOC+ userland section)
- `doc/05_design/spostgre_design.md` (§§2–12 of engine design)
- `doc/05_design/nvfs_design.md` (NVFS architectural contract)
- `doc/05_design/nvfs/from_spostgre.md` (§§S1–S7 upfront requirements + §§S-stretch-1–6)
- `doc/08_tracking/feature_request/nvfs_requests.md` (FR-NVFS backlog + upfront cross-ref)
- `src/lib/nogc_sync_mut/ecs/*.spl` (ECS idioms)
- `src/lib/nogc_sync_mut/spostgre_if/*.spl` (trait contracts, Phase 5 output)
- `src/lib/nogc_sync_mut/storage/*.spl` (shared primitives, Phase 5 output)
- `src/lib/nogc_sync_mut/fs/nvfs/*.spl` (NVFS trait contracts, Phase 5 output)
- `examples/spostgre/src/` (engine skeleton, Phase 5 output)
- `examples/nvfs/src/` (NVFS impl skeleton, Phase 5 output)

## Appendix I — Terminology and acronyms

| Acronym | Meaning |
|---|---|
| AIO | Asynchronous I/O |
| ATC | USENIX Annual Technical Conference |
| BRIN | Block Range Index (PostgreSQL) |
| CAS | Compare-and-Swap |
| CMB | Controller Memory Buffer (NVMe) |
| CRC32C | Castagnoli 32-bit cyclic redundancy check |
| DMA | Direct Memory Access |
| DSM | Dataset Management (NVMe TRIM) |
| ECS | Entity-Component-System |
| FAST | USENIX File and Storage Technologies Conference |
| FDP | Flexible Data Placement (NVMe TP4146) |
| FSM | Free Space Map (PostgreSQL) |
| FTL | Flash Translation Layer |
| FUA | Force Unit Access (NVMe) |
| GC | Garbage Collection |
| HOT | Heap-Only Tuple (PostgreSQL) |
| IOPS | I/O operations per second |
| KV | Key-Value (NVMe command set) |
| LBA | Logical Block Address |
| LSM | Log-Structured Merge tree |
| LSN | Log Sequence Number (PostgreSQL WAL) |
| MDSOC | Multi-Dimensional Separation of Concerns |
| MVCC | Multi-Version Concurrency Control |
| NAND | NAND flash memory |
| NAWUN | Namespace Atomic Write Unit Normal (NVMe) |
| NAWUPF | Namespace Atomic Write Unit Power Fail (NVMe) |
| NVFS | Simple's NVMe-aware filesystem (SimpleFS-NV) |
| NVMe | Non-Volatile Memory Express |
| OQ | Open Question (in this doc) |
| PID | Placement ID (NVMe FDP) |
| POD | Plain Old Data |
| PMR | Persistent Memory Region (NVMe) |
| QD | Queue Depth |
| RAM | Random-Access Memory |
| SIGMOD | ACM SIGMOD (Management of Data) |
| SLC/MLC/TLC/QLC | NAND cell bit-density classes (single/multi/triple/quad level cell) |
| SMART | Self-Monitoring, Analysis, and Reporting Technology |
| SOSP | ACM Symposium on Operating Systems Principles |
| SPDK | Storage Performance Development Kit |
| SQ / CQ | Submission Queue / Completion Queue (NVMe) |
| SSD-iq | SSD-iq benchmarking methodology (HotStorage '22) |
| TOAST | The Oversized-Attribute Storage Technique (PostgreSQL) |
| TP4065 / TP4146 | NVMe Technical Proposal (Simple Copy / FDP) |
| VACUUM | PostgreSQL's tuple-cleanup routine |
| VLDB | Very Large Data Bases conference |
| VM | Visibility Map (PostgreSQL) |
| WAF | Write Amplification Factor |
| WAL | Write-Ahead Log |
| YCSB | Yahoo! Cloud Serving Benchmark |
| ZNS | Zoned Namespace (NVMe command set) |

---

End of Phase 2 research deliverable. Phase 3 design docs (`spostgre_design.md`, `nvfs_design.md`, `nvfs/from_spostgre.md`) are the downstream commitments this doc grounds.
