# Research Report: NVMe SSD Firmware Architecture, FTL Mapping, Logging, Recovery, and Verification Plan

> **Status:** Research input (Step 1). Captured 2026-06-29. Drives the
> `examples/09_embedded/simpleos_nvme_fw` example and the parallel-agent build plan
> at `doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md`.
>
> **Validation:** load-bearing claims were web-validated and adversarially verified by the
> `nvme-fw-research-extend` workflow; see `research_addendum_2026-06-29.md` (40 cited sources,
> 16 verdicts). Factual refinements from that pass (NVMe spec family/transports/revision, SPDK
> lock-free I/O path, chunk/zone FTL metadata, FSCQ=Coq, LightNVM removed in Linux 5.15) are
> folded into §1/§2/§10/§13 below; the addendum holds the full corrections table and citations
> and is authoritative where it marks a claim corrected.

## 0. Requested requirements

Goal: design NVMe SSD firmware and research recovery algorithms, prevention algorithms,
FTL mapping strategies, and metadata logging strategies. The target should support a
simple OS or bare-metal runtime where possible.

Architecture requirements to include:

| # | Requirement | Interpretation for firmware design |
|---|-------------|-----------------------------------|
| 1 | Fully coroutine-based | All long operations are modeled as resumable tasks: NVMe command processing, mapping lookup, NAND program/read, GC, recovery, flush, trim, reset. |
| 2 | State-machine memory variables over local variables | Important state lives in persistent coroutine/task context objects, not volatile call-stack locals. This helps crash/debug tracing, timeout recovery, and formal modeling. |
| 3 | Index pointer with object pool | Use bounded object pools and generation-checked handles instead of raw pointers: `{pool_id, index, generation}`. |
| 4 | MDSOC+ architecture | Treat this as the project's modular/multi-domain SoC architecture: host, runtime, FTL, media, recovery, offload, verification. "MDSOC+" is used here as the architecture label (not a standard SSD-firmware term). |
| 5 | Highly offloadable to controller | Firmware calls abstract operations that can run in software or be offloaded to controller hardware: DMA, CRC, ECC, XOR/RAIN, bitmap scan, map lookup, compression/encryption, queue placement. |
| 6 | Formal verification with Lean4 under limited resources | Verify incrementally: object pools, queues, coroutine ownership, hang/timeout behavior, FTL logical correctness, crash recovery, GC, and multicore queue ownership. Full C firmware verification is staged after model-level proofs. |
| 7 | Dynamic load code funcs in embedded | Support only sandboxed, signed, bounded policy hooks at first: GC scoring, QoS policy, telemetry filter, hot/cold classifier. Do not dynamically load core recovery or metadata-commit code early. |

---

## 1. Executive thesis

A good first design is not a complex learned FTL or fully dynamic firmware. The recommended
starting point is:

> Bare-metal/simple-OS cooperative coroutine firmware + bounded object pools + generation
> handles + page-level/band log-structured FTL + DFTL-style mapping cache + checkpoint/WAL/P2L
> recovery + incremental Lean4 model verification.

NVMe was designed specifically for SSDs and supports scalable host communication over PCIe and
other transports (RDMA, TCP, Fibre Channel). The current NVMe family (Base Revision 2.3,
2025-08-05) is split into five document categories — Base, Command Set, Transport, Management,
and Boot — and defines multiple command sets including NVM, Zoned Namespace (ZNS), Key Value
(KV), Computational Programs, and Subsystem Local Memory. This makes an offload-capable design
natural, but the firmware core still needs a simple, deterministic command and metadata model.

The runtime should look closer to SPDK-style poll-mode asynchronous design than to a
preemptive embedded RTOS. SPDK's NVMe driver is asynchronous, passive, and **lock-free on the
I/O path** (queue pairs hold no locks or atomics; single-thread-per-queue-pair is an unenforced
caller requirement), designed around queue pairs, direct MMIO/DMA, callbacks, and
per-thread/per-core ownership; these ideas translate well to bare-metal SSD firmware.

For very small firmware, a stackless coroutine model is realistic: Protothreads demonstrate
that event-driven C code can be written as lightweight stackless threads, can run with or
without an OS, and can have extremely small RAM overhead. The design should use the same idea
but with explicit firmware task contexts instead of hidden stack state.

---

## 2. Key papers and systems: summary and comparison

| Area | Paper / system | Main idea | What to reuse | Caution |
|------|----------------|-----------|---------------|---------|
| NVMe baseline | NVMe specifications (Base Rev 2.3) | Five document categories (Base, Command Set, Transport, Management, Boot); command sets NVM/ZNS/KV/Computational Programs/Subsystem Local Memory; transports PCIe/RDMA/TCP/FC. | Use NVMe queue architecture as the outer protocol. Separate admin path, I/O path, reset path, error path, and telemetry path. | Do not design FTL around host API only; internal metadata consistency is harder than command parsing. |
| Async firmware architecture | SPDK NVMe driver and event framework | Poll-mode, asynchronous, lock-free-I/O-path model with per-core queue-pair ownership and message passing. | Model SSD firmware as reactors, pollers, queues, and asynchronous coroutine completions. | SPDK is host-side/userspace; firmware must adapt the design to controller cores, interrupts, DMA engines, and NAND schedulers. |
| Bare-metal coroutine model | Protothreads (Dunkels et al., SenSys 2006) | Stackless, memory-light coroutines for event-driven embedded systems, usable with or without an OS. | Use explicit coroutine state fields: phase, wait object, timeout, resource handles, last-progress timestamp. | Macros hide control flow and cannot keep local variables across a blocking wait. For verifiability, prefer generated or explicit state machines. |
| Mapping-cache FTL | DFTL (Gupta et al., ASPLOS 2009) | Demand-based FTL that caches only active page-level mappings in limited SSD RAM. | Use page-level L2P mapping with a bounded cache and flash-resident map pages. | Mapping-cache misses cause extra reads. Recovery and map-page consistency must be designed carefully. |
| Hybrid log-block FTL | FAST — Fully-Associative Sector Translation (Lee et al., ACM TECS 6(3), 2007) | Overwritten sectors can go into any log block (fully associative), reducing log-block thrashing vs BAST. | Useful for small-RAM baseline and historical comparison. | Hybrid FTLs are harder with modern high-parallelism NAND and large NVMe queues; page/band log FTL is usually cleaner. |
| Hybrid FTL crash recovery | FastCheck | Periodic checkpointing for FAST-style log-page mapping to improve crash recovery. | Use the principle: frequent compact checkpoints plus bounded log replay. | Specific to hybrid FAST-like FTL; adapt the checkpoint idea, not necessarily the whole FTL. (See addendum for citation status.) |
| Low-WA recovery | GeckoFTL (SIGMOD 2016) | Lazy recovery with checkpoints to reduce conflict between write amplification and recovery time. | Important design lesson: avoid forcing frequent dirty-map flushes only to bound recovery. | More complex than a first prototype; use after the basic WAL/checkpoint/P2L scheme works. |
| Modern open-source FTL | SPDK FTL | Band-based FTL; persists superblock, L2P, band metadata, valid map, chunk/zone metadata, P2L, trim metadata; dirty shutdown rebuilds L2P from P2L + sequence IDs. | Reference design for metadata layout: checkpointed L2P + per-band/per-chunk P2L + sequence ordering. | SPDK FTL is a software/device abstraction; embedded NAND still needs ECC, bad-block, plane/channel timing, and power-fail rules. |
| Power-failure testing | "Understanding the Robustness of SSDs under Power Fault" (Zheng et al., FAST 2013) | Tested commodity SSDs under thousands of injected power faults; many showed bit corruption, shorn/unserializable writes, metadata corruption, or total failure. | Build power-cut fault injection from day one. Every metadata update must be crash-point tested. | Simulators alone are insufficient; later test on hardware/emulator with forced reset/power-loss points. (Exact device/cycle counts: see addendum.) |
| Many-core SSD firmware | DeepFlash | Manycore SSD firmware platform for scalable NVMe-era parallelism; addresses firmware compute bottlenecks and contention. | Use domain sharding, per-core ownership, and queues between layers. | Multi-core should come after single-core invariants are verified. |
| Open SSD platform | Cosmos+ OpenSSD | OpenSSD platform with NVMe manager and FTL firmware organization; implements a subset of the NVMe command set. | Good experimental platform/reference for firmware decomposition. | Not a separately-named "low-level scheduler" component; existing firmware is not coroutine-verified or recovery-complete. |
| Host/device FTL split | LightNVM / Open-Channel SSD | Exposed SSD parallelism/media to the host; host could control placement, GC, scheduling. | Useful comparison for controller-offload and host-visible policy experiments. | **Removed from Linux in 5.15 (2021), superseded by ZNS.** Standard NVMe SSD firmware still needs internal FTL unless using a ZNS-style model. |
| Crash-consistency verification | FSCQ / Crash Hoare Logic (Chen et al., SOSP 2015) | Machine-checked crash recovery proofs (in **Coq**); crash condition and recovery procedure are part of the spec. | Copy the proof style: prove recovery after any crash point yields the old state or latest committed state. | FSCQ is Coq/filesystem work; no FSCQ-scope Lean4 crash-consistency verifier exists as of mid-2026 — the report's Lean4 plan owns that gap. |
| Lean4 verification | Lean | Open-source programming language and proof assistant for formally verified code. | Use Lean4 for executable models, invariants, refinement lemmas, and generated tests. | Keep scope small: verify models and protocols first, not the entire optimized firmware binary. Veil (CAV 2025) targets distributed/transition-system protocols, not storage crash-consistency. |
| Dynamic firmware hooks | eBPF / sandboxed bytecode idea | eBPF safely extends privileged kernels via a static verifier, bounded loops, maps, helpers, and optional JIT. | Use eBPF-like restrictions: signed modules, no raw pointers, bounded loops, fuel counter, typed handles. | Do not allow loaded code to mutate metadata journal, checkpoint, recovery, or NAND commit order. |

---

## 3. FTL mapping strategy comparison

| FTL strategy | RAM cost | Write amplification / performance | Recovery complexity | Bare-metal suitability | Recommendation |
|--------------|----------|-----------------------------------|---------------------|------------------------|----------------|
| Full page-level L2P in RAM | Very high | Excellent random-write behavior; simple lookup | Medium: must persist map safely | Good for simulator or small SSD | Use in Phase 1 simulator/prototype only. |
| DFTL-style cached page mapping | Medium/low | Good when locality is high; misses require extra map reads | Higher: dirty map cache and map-page ordering matter | Good | **Recommended** for real limited-RAM firmware. DFTL caches active mapping entries and stores full mapping in flash. |
| Block-level mapping | Low | Poor random writes; high write amplification | Low/medium | Simple | Not recommended except for teaching or tiny firmware. |
| Hybrid log-block mapping, FAST-like | Low/medium | Better than BAST because log blocks are fully associative | Medium/high | Possible | Good comparison design, but not the main recommendation for NVMe-era SSD. |
| Band/log-structured page FTL with P2L | Medium | Good sequentialization, good parallelism, natural GC | Medium, but robust if P2L + checkpoint + sequence IDs are used | Very good | **Main recommendation.** Same metadata principles as SPDK FTL: L2P, valid map, band/chunk metadata, P2L, trim metadata, dirty-shutdown L2P rebuild. |
| Learned FTL / regression mapping | Potentially low | Can be excellent for patterned workloads | High | Research-stage | Later experiment only. Do not use for first reliable firmware. |

**Recommended mapping design:** band-based, log-structured page-level FTL with a DFTL-like
mapping cache. In RAM, keep hot L2P entries, active-band state, valid-bitmaps for active/GC
bands, block erase counts, and dirty metadata descriptors. In flash, persist checkpoints, map
pages, P2L records, band summaries, valid maps, bad-block table, and sequence-numbered
journal entries.

---

## 4. Metadata logging and recovery strategy comparison

| Strategy | Runtime overhead | Recovery time | Crash consistency | Best use |
|----------|------------------|---------------|-------------------|----------|
| Full checkpoint only | High if frequent; low if rare | Fast if recent, slow/stale otherwise | Weak unless checkpoint is atomic | Not enough alone. |
| Delta WAL only | Medium | Replay can grow large | Good if journal ordering is strict | Useful but needs checkpoint compaction. |
| P2L scan only | Low runtime overhead | Can be slow on large devices | Good if OOB/P2L records have sequence and CRC | Good fallback, not enough alone for fast boot. |
| Checkpoint + WAL | Medium | Bounded replay | Good | Strong baseline. |
| Checkpoint + WAL + per-band P2L | Medium | Fast and robust | Excellent | **Recommended.** SPDK FTL uses persisted L2P/P2L metadata and can rebuild dirty L2P pages from P2L after dirty shutdown. |
| Shadow/COW map pages | Medium/high | Fast | Excellent if implemented correctly | Good for map-page persistence. |
| Capacitor-backed PLP | Hardware cost | Fast | Stronger guarantee for volatile cache flush | Use if hardware supports; firmware must still recover without trusting PLP blindly. |

**Recommended logging policy — three layers:**

1. **Superblock A/B** — firmware metadata version, checkpoint pointer, journal head/tail,
   generation, feature flags, and CRC.
2. **Checkpoint region** — compact L2P/map-page roots, band table, valid-map summary,
   erase-count summary, free-block state, bad-block table, and trim state.
3. **Journal + P2L records** — WAL records describe committed logical updates. P2L records in
   band metadata or OOB let recovery reconstruct L2P by scanning only dirty/open/recent bands
   instead of the whole device.

---

## 5. Proposed MDSOC+ firmware architecture

"MDSOC+" = the project's Modular / Multi-Domain SoC+ SSD firmware architecture label.

| Domain | Responsibilities | Coroutine tasks | Offload candidates |
|--------|------------------|-----------------|--------------------|
| Host Interface | NVMe admin queue, I/O SQ/CQ, doorbells, PRP/SGL, DMA setup, namespace state | `nvme_admin_task`, `nvme_io_task`, `reset_task`, `flush_task` | Doorbell handling, DMA descriptor walking, PRP/SGL translation |
| Firmware Runtime | Reactor loop, timers, watchdog, object pools, queues, cancellation, telemetry | `reactor_task`, `timer_task`, `watchdog_task`, `pool_audit_task` | Queue storage in controller memory, interrupt coalescing |
| FTL Core | L2P/P2L, map cache, write allocator, GC, trim, wear leveling | `write_task`, `read_task`, `map_fetch_task`, `gc_task`, `trim_task` | Map lookup assist, bitmap scan, GC scoring |
| Metadata/Recovery | WAL, checkpoints, superblock, dirty shutdown recovery, rollback | `journal_task`, `checkpoint_task`, `recovery_task` | CRC, journal scan, metadata copy |
| Media | NAND read/program/erase, channel/plane scheduler, ECC, bad block, read retry | `nand_read_task`, `nand_prog_task`, `erase_task`, `ecc_task` | ECC/LDPC, RAID/RAIN XOR, copyback |
| Offload | Capability discovery, hardware abstraction, fallback software path | `offload_dispatch_task` | All optional controller accelerators |
| Verification | Lean4 models, invariants, trace checking, generated tests | (not runtime-critical) | Runtime assertion generation, model checking, trace replay |

This maps naturally to NVMe's queue-rich design. Many-core SSD research such as DeepFlash
argues that firmware compute and contention can become bottlenecks under NVMe-level
parallelism.

---

## 6. Bare-metal / simple-OS execution model

The firmware runs as a cooperative reactor:

```
main()
  init_static_memory()
  init_object_pools()
  init_nvme()
  init_media()
  init_recovery_or_clean_boot()

  while true:
      poll_nvme_queues()
      poll_dma()
      poll_nand_channels()
      run_ready_coroutines()
      run_timers()
      run_watchdog()
      maybe_checkpoint()
```

**Core rules**

| Rule | Reason |
|------|--------|
| No blocking wait inside firmware tasks | Prevents global stalls and makes hang detection tractable. |
| ISRs only enqueue events | Keeps interrupt logic short and verifiable. |
| No heap allocation after init | Object pools are bounded and easier to verify. |
| Important state is stored in task context | A coroutine can yield, timeout, cancel, or be inspected without losing critical variables. |
| No raw pointer across yield | Use generation-checked handles to avoid stale pointer bugs. |
| One owner per mutable resource | Makes multicore correctness much simpler. |
| Every task has a timeout and progress marker | Enables hang detection and recovery. |

---

## 7. Object pool and index-pointer design

Use handles instead of raw pointers:

```c
typedef struct { uint16_t pool_id; uint16_t index; uint32_t generation; } ObjId;

typedef enum {
    SLOT_FREE, SLOT_ALLOCATED, SLOT_QUEUED, SLOT_RUNNING,
    SLOT_WAITING, SLOT_COMPLETING, SLOT_CANCELLED
} SlotState;

typedef struct {
    uint32_t generation;
    SlotState state;
    uint16_t owner_core;
    uint16_t type;
    uint64_t last_progress_tick;
    uint32_t refcnt;
    uint8_t payload[];
} PoolSlot;
```

**Required invariants**

| Invariant | Purpose |
|-----------|---------|
| `free_count + allocated_count == pool_capacity` | Detect leaks and double allocation. |
| Handle generation must match slot generation | Detect stale handle reuse. |
| A queued object belongs to exactly one queue | Prevent duplicate execution. |
| A running object has exactly one owner core | Prevent data races. |
| A cancelled object eventually reaches free or completed | Prevent cancellation leaks. |
| Every allocated task has a timeout or parent | Prevent orphan hangs. |

This is one of the best places to start Lean4 verification: small state space, high invariant value.

---

## 8. Coroutine state-machine model

Every firmware operation is a coroutine object:

```c
typedef enum {
    PHASE_INIT, PHASE_MAP_LOOKUP, PHASE_MAP_FETCH, PHASE_ALLOC_PPN,
    PHASE_DMA_IN, PHASE_NAND_PROGRAM, PHASE_JOURNAL_COMMIT, PHASE_UPDATE_L2P,
    PHASE_COMPLETE_HOST, PHASE_ERROR_RECOVERY, PHASE_DONE
} WritePhase;

typedef struct {
    ObjId self; ObjId host_cmd; ObjId dma_req; ObjId nand_req; ObjId journal_req;
    WritePhase phase;
    uint64_t lba; uint32_t nblocks;
    uint64_t old_ppn; uint64_t new_ppn; uint64_t map_page_id; uint64_t seq;
    uint32_t retry_count; uint64_t deadline_tick; uint64_t last_progress_tick; int error;
} WriteTask;
```

This satisfies the "state-machine memory variables over local variables" requirement.
Local variables may still be used for temporary arithmetic, but anything needed after yield,
timeout, crash tracing, cancellation, or verification belongs in the task object.

---

## 9. Recommended FTL design

### 9.1 Data layout

```
[Superblock A] [Superblock B]
[Checkpoint Region 0] [Checkpoint Region 1]
[Map Page Area]  - L2P map pages, map-page root/index, dirty-map generation
[Journal/WAL Area]  - MAP_COMMIT, TRIM, GC_MOVE, CHECKPOINT_BEGIN/END records
[Data Bands]  - user pages; per-page OOB {LPN, seq, CRC, flags}; per-band P2L summary; valid bitmap
[Bad Block / Erase Count / Wear Metadata]
```

### 9.2 Write path

```
NVMe write -> alloc WriteTask -> DMA host data -> lookup L2P (fetch map page on miss)
  -> choose free physical page from active band
  -> program NAND page with OOB {LPN, seq, CRC}
  -> append WAL MAP_COMMIT {LPN, old_ppn, new_ppn, seq}
  -> update RAM L2P -> mark old PPN invalid -> update valid map/band state
  -> complete NVMe command
```

The key decision is **when to acknowledge the host**. Reliable mode: ack only after the data
page and enough metadata exist to recover the mapping. With power-loss protection, a faster
policy is possible, but a conservative mode should be retained.

### 9.3 Read path

```
NVMe read -> alloc ReadTask -> lookup L2P (fetch map page on miss)
  -> NAND read -> ECC/read-retry if needed -> DMA to host -> complete
```

### 9.4 Trim path

```
NVMe DSM/deallocate -> alloc TrimTask -> append TRIM to WAL
  -> set L2P entry invalid/null -> invalidate old physical pages -> complete
```

### 9.5 Garbage collection path

```
GC trigger -> choose victim band (valid-count, erase count, age, temperature)
  -> for each valid page: read; verify still latest; move to new page; append GC_MOVE; update L2P
  -> erase victim block/band -> update erase count and free list
```

GC must be fully transactional: a crash during GC must never lose the old valid copy until
the new copy is durable and discoverable during recovery.

---

## 10. Recovery algorithms

### 10.1 Dirty shutdown recovery

1. Read Superblock A/B.
2. Choose latest valid superblock by generation and CRC.
3. Load latest complete checkpoint.
4. Reconstruct base L2P/map roots, band table, free list, bad-block table.
5. Replay WAL records after checkpoint.
6. Scan P2L records for open/dirty/recent bands. (Open bands keep their P2L in a separate
   cache-device metadata region; closed bands store it in band tail metadata.)
7. For each LPN, choose physical page with highest valid sequence number.
8. Rebuild dirty L2P entries.
9. Rebuild valid bitmaps.
10. Repair free-block lists.
11. Write recovery-complete checkpoint.
12. Start normal NVMe service.

Aligned with the SPDK FTL principle: persisted metadata includes superblock, L2P, band and
chunk/zone metadata, valid maps, P2L, and trim metadata; after dirty shutdown, L2P is rebuilt
from per-band/per-chunk P2L maps and sequence IDs.

### 10.2 Crash points to test

| Crash point | Required recovery result |
|-------------|--------------------------|
| Before NAND program | Old mapping remains valid. |
| After NAND program, before WAL | Recovery may ignore new page unless P2L scan makes it discoverable and policy allows it. |
| After WAL, before RAM L2P update | WAL replay installs new mapping. |
| After RAM L2P update, before checkpoint | WAL/P2L reconstructs new mapping. |
| During GC copy | Either old page or new page is chosen; never neither. |
| During block erase | Block must not be erased until all live mappings moved and committed. |
| During checkpoint write | Previous checkpoint remains valid unless new checkpoint has complete marker and CRC. |
| During superblock update | A/B superblock selection must pick the latest complete version. |

### 10.3 Queue and hang recovery

| Failure | Detection | Recovery |
|---------|-----------|----------|
| NAND command timeout | Per-command deadline | Reset channel/die; retry idempotent op; escalate to bad block if repeated. |
| DMA timeout | DMA deadline + descriptor state | Abort DMA, reset engine, fail or retry host command. |
| Coroutine hang | `last_progress_tick` not updated | Cancel task, release resources via parent cleanup path, emit telemetry. |
| Object pool leak | Pool audit mismatch | Quarantine affected task tree, dump trace, enter degraded mode or assert in debug. |
| Queue stuck | Head unchanged + nonempty + no owner progress | Reassign owner or reset queue domain. |
| Multicore ownership bug | Owner mismatch assertion | Stop accepting new commands, preserve crash dump, reset firmware domain. |

---

## 11. Prevention algorithms

| Risk | Prevention algorithm |
|------|----------------------|
| Metadata corruption | A/B superblock, CRC everywhere, generation counters, COW checkpoints, journal replay. |
| Power loss | Conservative host-completion point, WAL ordering, P2L records, frequent bounded checkpoints, optional PLP. |
| Write amplification | Hot/cold separation, band-based sequential writes, GC victim scoring, overprovisioning reserve, trim. |
| Free-block exhaustion | Hard GC threshold, emergency reserve blocks, host throttling before reserve depletion. |
| Wear imbalance | Dynamic wear leveling for hot data; static wear leveling to move cold data off low-wear blocks. |
| Read disturb | Read counters, refresh migration, read retry, ECC margin tracking. |
| Program/erase failure | Bad-block retirement, remapping, spare block reserve. |
| Die/channel failure | Internal RAID/RAIN parity where hardware budget allows. |
| Firmware hang | Coroutine deadlines, watchdog, bounded queues, no blocking waits, progress counters. |
| Stale pointer / use-after-free | Generation-checked object IDs, no raw pointer across yield. |
| Queue overflow | Bounded queue proofs, backpressure, NVMe command throttling. |
| Dynamic code fault | Sandboxed hooks, signed modules, bounded execution, no raw metadata pointers. |
| Thermal overload | Temperature-aware throttling and GC pacing. |

Power-fault testing must be a first-class part of validation: the Zheng et al. (FAST 2013)
study of commodity SSDs found many devices exposed serious failures under injected power
faults (corruption, metadata failures), so metadata ordering must be tested under repeated
crash injection, not assumed correct.

---

## 12. Offloadable controller design

```c
typedef struct {
    bool dma_sgl_walk; bool crc32c; bool ecc_ldpc; bool xor_rain; bool bitmap_scan;
    bool map_cache_hash; bool compression; bool encryption; bool cmb_queue_memory;
    bool computational_programs;
} ControllerCaps;
```

Firmware calls abstract operations (`ops->crc32c(...)`, `ops->select_gc_victim(...)`,
`ops->xor_build_parity(...)`, `ops->dma_submit(...)`). Each resolves to: hardware offload if
supported → optimized firmware implementation → simple reference implementation.

**Good offload targets:** DMA PRP/SGL walking, CRC/checksum, ECC/LDPC, XOR/RAIN parity, valid
bitmap scan, map-cache hash lookup, compression/encryption, copy/compare/memset, queue memory
in controller memory (CMB).

**Do not offload correctness policy first.** Offload deterministic sub-operations first; keep
metadata ordering, journal commit, recovery decisions, and GC transaction state in verified
firmware until the offload interface is proven.

---

## 13. Lean4 formal verification plan

Model-first verification. Note: FSCQ and Crash Hoare Logic (the proof-style inspiration) are
implemented in **Coq**; no FSCQ-scope Lean4 crash-consistency verifier exists as of mid-2026,
so this plan deliberately owns that gap with model-level Lean4 proofs.

| Phase | Model | Prove |
|-------|-------|-------|
| A | Object pool | No stale handle resolves; no double allocation; capacity preserved; generation check prevents use-after-free. |
| B | Bounded queue | FIFO ordering; no overflow without explicit failure; dequeue returns queued objects only once. |
| C | Coroutine resource protocol | Every allocated child object is released on success, error, timeout, or cancel. |
| D | Single-core command model | Read-after-write correctness; trim semantics; command completion only after required durable point. |
| E | WAL/checkpoint recovery | After any crash point, recovery returns either previous committed state or latest committed state. |
| F | P2L/L2P consistency | Every valid L2P entry points to a physical page whose P2L says the same LPN and latest sequence. |
| G | GC correctness | Moving valid pages preserves logical read result; erased victim contains no latest valid mappings. |
| H | Multicore queues | Single ownership of mutable objects; no object running on two cores; message passing preserves ownership. |
| I | Hang model | A task either progresses, waits on a declared event, times out, or is cancelled. |

**Important invariants**

```
Pool:     free + allocated = capacity
          valid(handle) -> slot.generation == handle.generation
          slot.state == FREE -> no valid external handle
Queue:    len <= capacity; every queued id resolves to allocated slot; no duplicate id in same queue
FTL:      L2P[lpn] = ppn -> P2L[ppn].lpn = lpn
          latest_seq(lpn) determines visible data
          valid_bitmap[ppn] = true iff ppn is latest or protected during GC
          erase(block) allowed only if live_count(block) = 0
Recovery: recover(crash(trace)) = committed_prefix(trace)
          checkpoint valid only if END marker and CRC valid
          newer superblock chosen only if generation and CRC valid
Multicore: mutable object has one owner; queue transfer changes owner at dequeue boundary
```

Proof inspiration: FSCQ and Crash Hoare Logic, where recovery behavior is part of the
specification and proven under arbitrary crash/reboot sequences.

---

## 14. Dynamic loaded code functions in embedded firmware

Dynamic code is useful but dangerous in SSD firmware (metadata corruption can brick the
device). Use it only for bounded policy hooks.

**Allowed early hooks**

| Hook | Safe input | Safe output |
|------|-----------|-------------|
| GC victim scoring | Read-only band stats | Score number |
| QoS priority | Command class, namespace, age | Priority class |
| Hot/cold classifier | LBA, write frequency, stream ID | Temperature class |
| Telemetry filter | Counters/logs | Filtered report |
| Background throttle policy | Temperature, free blocks, latency | Throttle level |

**Forbidden early hooks:** WAL commit ordering, checkpoint writer, superblock update,
bad-block table mutation, raw NAND program/erase sequencing, direct pointer manipulation.

**Recommended sandbox model** (eBPF-like / tiny-WASM-like): signed module, versioned ABI, no
raw pointers, only typed handles, bounded loops or fuel counter, fixed memory budget, no
blocking calls, no direct journal writes, verifier before install, watchdog during execution,
rollback to default policy on fault.

---

## 15. Development roadmap

| Phase | Build | Verification / testing goal |
|-------|-------|------------------------------|
| 0 | NAND + NVMe firmware simulator | Trace every command, crash point, queue event, object-pool transition. |
| 1 | Object pool + queue library | Lean proofs for pool/queue invariants; C runtime assertions generated from model. |
| 2 | Single-core coroutine runtime | No blocking; timeout/cancel cleanup; deterministic trace replay. |
| 3 | Simple page-level FTL | Full RAM L2P first; prove read-after-write and trim semantics. |
| 4 | WAL + checkpoint + crash recovery | Crash after every metadata step; prove/replay committed-prefix property. |
| 5 | P2L-based recovery | Rebuild dirty L2P from P2L and sequence numbers. |
| 6 | DFTL-style map cache | Add map-page reads/writes, dirty cache, eviction, map-page checkpointing. |
| 7 | GC + wear leveling | Prove GC preserves logical view; test free-block exhaustion. |
| 8 | Multicore queues | Shard by namespace, LBA range, band, or channel; prove single ownership. |
| 9 | Controller offload abstraction | Add software fallback for every hardware operation. |
| 10 | Dynamic policy hooks | Sandboxed GC/QoS/telemetry hooks only. |
| 11 | Hardware/emulator validation | NVMe compliance, power-cut injection, endurance, thermal, reset, timeout tests. |

---

## 16. Recommended first implementation target

**Minimal reliable prototype**

- Bare-metal or tiny cooperative kernel; one reactor core; static memory only.
- Object pools: `HostCmdPool`, `FtlTaskPool`, `DmaReqPool`, `NandReqPool`, `JournalReqPool`, `TimerPool`.
- Full RAM L2P for tiny simulated NAND.
- WAL + A/B checkpoint.
- P2L in OOB or simulated spare metadata.
- Crash injection after every state transition.
- Lean proofs for pool, queue, L2P/P2L consistency, recovery.

**Then scale to realistic firmware** — replace full L2P with DFTL-style map cache; add band
allocator; add GC; add wear leveling; add multi-channel scheduler; add multicore queue
ownership; add offload capability table; add sandboxed policy hooks.

---

## 17. Final design recommendation

```
NVMe queues
  -> coroutine runtime
  -> verified object pools and queues
  -> FTL task graph
  -> page/band log-structured mapping
  -> checkpoint + WAL + P2L recovery
  -> NAND scheduler
  -> optional controller offload
  -> sandboxed dynamic policy hooks
```

The most important early decision is to make **recovery and verification architectural, not an
afterthought**. A fast FTL that cannot prove recovery behavior is not a reliable SSD firmware
base. Start with the simplest verifiable FTL, then add DFTL caching, GC, multicore queues,
offload, and dynamic functions only after each resource and consumer model is verified.
