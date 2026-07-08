# NVMe firmware — production-hardening status & acceptance bar

**Scope (read this first).** This firmware is a **host-runnable simulation** of an NVMe SSD
controller, written in pure Simple. "Production level" here means **production-grade *logic*
and **NVMe protocol compliance**, validated in simulation** — *not* a binary shippable to
silicon. The simulation boundary is deliberate and unchanged:

- In scope (verified here): data-path correctness (no data-loss / host-hang defects), the
  mandatory NVMe admin + IO command surface with correct completion status codes, malformed
  input never crashing the controller, power-loss recovery as a real property (volatile state
  wiped, L2P + bad-block table rebuilt from NAND), wear-leveling + read-disturb-scrub *logic*,
  SMART/health telemetry wired to real activity, the safety-critical invariants proven in
  Lean4 (req 6), sandboxed dynamic policy hooks (req 7: install gate, output clamps, modeled
  fuel bound), live SMART composite temperature from the PowerThermal model (P7), and internal
  RAID/RAIN cross-channel XOR-parity rebuild with no logical data loss (P8).
- Out of scope (silicon-only — tracked, not built here): real BCH/Reed–Solomon hardware ECC,
  real register MMIO / PCIe transport, a persistent backing store, and multi-channel NAND
  timing. The bare-metal **rv32** scalar firmware floor is written, host-verified, and wired through
  the rv32 boot hook, including RAIN, ECC, scheduler, power/thermal, map-cache, band, journal,
  HIL/queue, task-pool fail-closed, IO/admin/flush, reactor, policy/target, DRAM/durability, wear/scrub, media-retire,
  power-cycle, backpressure/abort, feature/namespace guards, and the Cosmos+ OpenSSD target
  profile; the full no-alloc firmware port is not wired into that boot path yet (see also
  `BUILD_STATUS.md`). The sibling rv64 lane has a direct-build recipe and fail-closed real-boot
  SSpec, but the current build attempt terminates before `build/nvme_fw_rv64.elf`; see
  `doc/08_tracking/bug/nvme_fw_rv64_direct_build_timeout_2026-07-07.md`.

## Acceptance bar (the goal is met when every box is checked) — ✅ MET

- [x] **No known data-loss or host-hang defect.** Each fixed with a regression test that
      fails before the fix and passes after (or, where the audit was wrong, verified a non-bug):
  - [x] GC never erases a victim block while any live page is un-relocated — alloc-fail aborts
        GC (`reclaim_block`/`gc_once`; `gc_safety_check.spl`, `ftl_gc_safety_selftest`).
  - [x] A fetched command **always** posts a completion — no host-hang. (Audit claim of a silent
        drop on pool exhaustion was **verified a non-bug**: `hil.tick`/`io_process` post a
        completion for every command, and normal acquire→release within one synchronous tick
        cannot exhaust from queued backlog.)
  - [x] If task-pool metadata is unavailable or corrupt, HIL and multi-queue controller writes
        fail closed with `SC_NS_NOT_READY` and leave media unchanged
        (`task_pool_fail_closed_check.spl`).
  - [x] Journal overflow is surfaced — `ensure_journal_room` forces a checkpoint+truncate before
        appending, never a silent ack of a lost record (`durability_check.spl` 600-write case).
  - [x] A write that cannot allocate fails atomically (`SC_NS_NOT_READY`, no half-applied
        map/journal state); the GC reserve keeps the device live (no write-cliff).
- [x] **Protocol surface.** Mandatory admin commands handled with correct `SC_*` — Identify,
      Get/Set Features, Create/Delete IO SQ/CQ, Get Log Page, **Abort, Async Event Request,
      Format NVM, Firmware Download/Commit**; IO: Read/Write/Flush/Trim. Unknown opcode →
      `SC_INVALID_OPCODE`; LBA/NLB out of range → `SC_LBA_RANGE` with **no integer overflow**
      (the overflow bypass that could index `l2p[]` out of range is fixed). Invalid Identify
      Namespace requests and IO NSIDs are rejected before media access in the single-namespace
      model. Malformed input never crashes; negative-path tests at `cmd_validate`, the queue
      level, and the controller E2E gate.
- [x] **Durability.** A power cycle wipes *all* volatile DRAM state (write-back map cache + band
      valid bitmap); recovery replays the journal onto the flash-resident L2P, rebuilds the band
      bitmap, and re-applies the (persistent) bad-block table; committed writes survive, trims
      stay trimmed, retired blocks stay retired (`durability_check.spl`, `ftl_durability_selftest`).
- [x] **Media management.** Static wear-leveling (`wear_level_once`, erase-count-aware victim) and
      read-disturb scrubbing (`scrub_once`, per-block read counter) relocate data without loss
      (`wear_scrub_check.spl`, `ftl_media_mgmt_selftest`).
  - [x] **RAID/RAIN rebuild (P8).** A whole-channel uncorrectable failure is rebuilt in place from
        live-maintained XOR parity with no logical data loss (`rain_recover_channel`; `rain_seal` is
        the scrub/repair path;
        `rain_ftl_check.spl` → "RAIN-FTL OK"; `ftl_rain_selftest`; `fw/proofs/Rain.lean`).
- [x] **Health.** SMART reflects real activity (data units r/w, host cmd counts, power cycles,
  unsafe shutdowns, media errors, percent-used from erase counts, available spare from bad
  blocks, critical warning); an error log records failed commands (`nvme_controller_selftest`).
  The SMART composite temperature is now the **live `PowerThermal` value** (P7; was a hardcoded
  313 K) with the thermal critical-warning bit ORed in (`thermal_check.spl` → "THERMAL OK",
  `power_thermal_selftest`, and the two thermal assertions in `nvme_controller_selftest`).
- [x] **ECC is stored, decoded, and checked from NAND OOB.** The sim writes a compact SECDED
      payload-window ECC at program time into NAND spare-area state and reads it back through the
      ONFI/FMC latches; FIL corrects one silent payload-bit error through bit 16, detects double-bit
      payload corruption, and fails closed on stored-ECC/OOB metadata
      corruption (`fil_selftest`, `ecc_check.spl`).
- [x] **Segmented PRP host writes are load-bearing.** HIL and the multi-queue NVMe controller now
      write every LBA in `nblocks` from a modeled two-segment PRP byte stream instead of silently
      programming only the first block (`host_transport_check.spl`, `hil_selftest`,
      `nvme_controller_selftest`).
- [x] **DRAM pressure is explicit.** The live `Ftl` uses a bounded LRU write-back `ftl_map` cache
      whose capacity is tied to `MAP_CACHE_DRAM_BUDGET_BYTES`; dirty evictions write back to the
      flash-resident L2P. HIL and the multi-queue NVMe controller also stage host writes through a
      bounded DRAM arena span and reject over-budget writes before any partial media update
      (`ftl_map_selftest`, `dram_buffer_check.spl`).
- [x] **Foreground/background FTL access is serialized.** `Firmware.service()` now drains work
      through `service_tick()`, which gives each tick one foreground HIL command and one
      background-GC opportunity behind an explicit FTL-map owner token (`firmware_selftest`).
- [x] **Formal (req 6).** `fw/proofs/{Alloc,Recover,Gc,Hooks,Fmc,Rain}.lean` prove the
      allocator/GC-reserve, committed-prefix recovery, GC data-loss-guard, policy-hook, FMC, and
      RAIN cross-channel reconstruction invariants; each checks green with `lean`, and `Rain.lean`
      proves the P8 reconstruction formula.
- [x] **Sandboxed dynamic policy hooks (req 7).** Runtime-installable GC-score / QoS / hot-cold /
      telemetry hooks (`hooks.spl`) behind an install gate that rejects forbidden
      metadata/recovery/commit domains (`sandbox.spl`), with output clamps and a modeled fuel
      bound; the GC hook only *scores* the firmware's own CLOSED candidates (never names a block),
      so a malicious hook cannot corrupt the allocator or lose data (`policy_hooks_check.spl`,
      `hooks_selftest`/`sandbox_selftest`; proven in `fw/proofs/Hooks.lean`).
- [x] **Green + documented.** `test_fw`, `sim_main`, `nvme_main`, and the production self-tests
      pass via `bin/simple run`; the system sspec (incl. the Lean scenario) passes via
      `bin/simple test`; `doc/06_spec` regenerated at 0 stubs; this doc + `README`/`BUILD_STATUS`
      state the silicon boundary.

**Gap-closure vs. acceptance bar.** The acceptance bar above (req 1-7) is **MET** — that is *not* the
same as "all gap-closure / production work is done." Per
`doc/03_plan/hardware/nvme_fw_gap_closure_plan.md` § "Integration status": **P1** (`fil_fmc`), **P2**
(`fil_scheduler`), **P7** (`power_thermal`), and **P8** (`rain`) are **wired into the live
controller/FTL**; P2 is still a timing floor because a single-threaded sim cannot physically exhibit
channel-level parallelism; **P3 has a wired SECDED payload-window stored-ECC simulation floor** (not full BCH/LDPC); **P4 has a
wired segmented-PRP host-byte floor** (not full HostMem/SGL/IOMMU); **P5 has a wired bounded-map-cache
and fixed arena/free-list floor** (not a full DRAM subsystem); **P6 has a wired cooperative-owner floor** (not
multicore/preemptive); and **P9** has a host-verified rv32 scalar firmware floor wired through the
boot hook (including task-pool fail-closed coverage) plus an rv64 direct-build recipe whose ELF output is still blocked, while the full
no-alloc firmware port remains pending (see the silicon boundary below).

**Silicon boundary (unchanged).** Real BCH/Reed–Solomon/LDPC hardware ECC (the sim keeps a
stored SECDED payload-window ECC + injected-bit-error model), real register MMIO / PCIe transport, full PRP/SGL DMA,
real DRAM refresh/ECC/bandwidth, true multicore/preemptive concurrency, a persistent backing store, and multi-channel NAND timing remain out of scope; the bare-metal **rv32** scalar firmware floor is
written + host-verified, rv64 direct-build/real-boot evidence is still missing an ELF, and the
full no-alloc firmware port has not been wired into the boot paths yet.
"Production level" here = production-grade *logic and NVMe protocol compliance, simulation-validated*.

**Policy-hook sandbox boundary (req 7).** The real silicon trust boundary for dynamically loaded
policy code is cryptographic module signing + a static verifier; in-sim the boundary is the
**install gate** (only the four policy kinds load; metadata/recovery/commit domains are rejected),
**structural isolation** (a hook is a pure function of copied scalars with no FTL / NAND / journal
handle), and **output validation** (clamps; the GC hook only scores trusted CLOSED candidates, so
the chosen victim is always CLOSED — proven in `fw/proofs/Hooks.lean`). The per-invocation **fuel
bound is *modeled*** — a cooperative self-reported budget that discards over-budget votes, not a
hard preemption — so it is a liveness/QoS guard, not the safety claim.
