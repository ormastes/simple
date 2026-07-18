# NVMe FW — Gap-Closure Implementation Plan (simulation → hardware-faithful), with tests

> **Status (2026-07-07): WIRED SIMULATION FLOORS.** This plan tracks the closed simulation
> floors between `examples/09_embedded/simpleos_nvme_fw/fw/` (~5K LOC pure-Simple, run-green)
> and a real hardware-facing NVMe SSD firmware, as measured against the open comparators
> Cosmos+ OpenSSD GreedyFTL (runs on FPGA+ARM, NVMe 1.2/PCIe) and FEMU (QEMU NVMe emulator),
> and against commercial firmware ("millions of LOC, a miniature OS").
>
> **What "closing the gap" means here.** Each phase implements the missing concern
> **faithfully in the pure-Simple simulation** — register-level MMIO models, a real
> multi-channel scheduler, a real ECC codec, a byte-accurate DMA model — with tests and,
> where the property is provable in Lean core, a proof. This makes the simulation
> hardware-**faithful and verifiable**; it does **not** produce a silicon binary. The true
> silicon ceiling (real NAND timing/voltage, PCIe electrical, LDPC hardware, multi-core RTOS)
> stays out of scope and is stated per phase.
>
> **Sources of truth**
> - Comparison + verdict: this plan's "Gap inventory" below; web comparators
>   (Cosmos+ `GreedyFTL-2.7.0.d`: `fmc_driver.c`, `low_level_scheduler.c`, `lru_buffer.c`,
>   `page_map.c`, `nvme/`; FEMU bbssd page-FTL on QEMU).
> - Current scope + silicon boundary: `examples/09_embedded/simpleos_nvme_fw/fw/PRODUCTION_STATUS.md`,
>   `BUILD_STATUS.md` (deferred list), `README.md` (req coverage), research
>   `doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md` (§11 prevention,
>   §12 ControllerCaps, §15 roadmap).
> - Predecessor: `doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md` (phases 0–7 done).

## Gap inventory (from the real-firmware comparison)

| # | Gap | Today | Real firmware (Cosmos+/commercial) | Phase |
|---|-----|-------|-----------------------------------|-------|
| G1 | Flash-controller driver | simulated ONFI device, direct calls | `fmc_driver.c` register MMIO driver | P1 |
| G2 | Multi-channel/way parallelism | single channel, serial | `low_level_scheduler.c`, 8ch×8way | P2 |
| G3 | Real ECC | checksum + injected-flip | hardware BCH/LDPC | P3 |
| G4 | Host data transport | data passed as `i64` values | DMA scatter-gather (PRP/SGL) over PCIe | P4 |
| G5 | DRAM management | per-instance arrays | managed DRAM arena (buffer + map cache) | P5 |
| G6 | Concurrency (fg I/O vs bg tasks) | one synchronous tick | multi-core, shared FTL-map under locks | P6 |
| G7 | Power + thermal | none | NVMe power states + thermal throttle | P7 |
| G8 | Die/channel failure resilience | none | internal RAID/RAIN parity | P8 |
| G9 | Real embedded target | host interpreter | bare-metal SoC (rv32 no-alloc) | P9 |

## Integration status — wired vs. shelf (honest accounting)

A phase is only gap-closing once its module is **load-bearing** in the live firmware, not just
green against its own self-test. Tracking that explicitly so "DONE" never means "exists beside
the firmware":

| Phase | Module | Live caller | Status |
|-------|--------|-------------|--------|
| P1 | `fil_fmc` | `fil.spl` (every program/read/erase routes through the FMC handshake) | **wired** |
| P3 | `fil_ecc` + NAND OOB ECC latch | `fil.spl` reads stored ECC through `fil_fmc`, corrects one silent payload-window bit, and fails double-bit/OOB corruption closed | **wired SECDED payload-window floor** — not full BCH/LDPC |
| P4 | `hil_command.prp_byte` | HIL + multi-queue NVMe writes program each LBA from a segmented PRP host byte stream | **wired segmented-PRP floor** — no full HostMem/SGL/IOMMU yet |
| P5 | `ftl_map` + `dram` | `Ftl` uses bounded LRU write-back cache; HIL/controller writes allocate a bounded DRAM arena span before programming media | **wired DRAM floor** — no full DRAM subsystem yet |
| P6 | `firmware.service_tick` | Foreground HIL ticks and background GC ticks share an explicit FTL-map owner token | **wired cooperative floor** — no multicore/preemption |
| P7 | `power_thermal` | `nvme_controller` (IO path ticks it; SMART reports its temperature) | **wired** |
| P8 | `rain` | `ftl` (writes/GC/format maintain parity; `rain_recover_channel` rebuilds a failed channel inside the live FTL, verified end-to-end through the normal read path) | **wired** |
| P2 | `fil_scheduler` | `fil.spl` (every valid program/read/erase queues the target block through the scheduler before the FMC command) | **wired timing floor** — channel-level parallelism is still a model the single-threaded sim cannot physically exhibit |
| P9 | `fw_rv32/entry.spl`, `fw_rv64/build.shs` | bare-metal rv32 scalar firmware floor (re-expresses RAIN, ECC, fixed scheduler, fixed power/thermal, fixed map-cache, fixed band, fixed journal-ring, fixed HIL, fixed queue-phase, fixed task-pool fail-closed, fixed io-opcode-read-zero-trim-flush, fixed admin/format/fw-log, fixed reactor, fixed policy/target, fixed DRAM/durability, fixed wear/scrub, fixed media-retire, fixed power-cycle, fixed backpressure/abort, fixed feature/namespace guards, and the Cosmos+ OpenSSD target profile array-free; `check`-clean + host-verified); rv64 direct-build recipe plus fail-closed real-boot SSpec | rv32 wired through boot hook; rv64 ELF output blocked by native-build termination; full no-alloc firmware port remains the ceiling |

Adding more standalone modules (full P4 HostMem/PRP lists, full P5 DRAM refresh/ECC/bandwidth, multicore P6 beyond the cooperative token, or full BCH/LDPC beyond the P3 floor) widens the shelf without closing the gap. Prefer
wiring an existing verified module into the live path over landing a new disconnected one.

## Test discipline (applies to every phase)

Follow `fw/CONVENTIONS.md`. Each new module exposes `fn <module>_selftest() -> i64`
(0 = pass) gated by `bin/simple run` (not `check`). Each phase adds:
1. **Module self-test** (in `test_fw.spl`, kept < 10s total).
2. **A standalone `*_check.spl`** runnable for the adversarial/property cases (printed
   `… OK` marker), gated as a `_run` `it` in
   `test/03_system/app/nvme_firmware/nvme_firmware_simulation_spec.spl`, then
   `spipe-docgen … --output doc/06_spec` at 0 stubs.
3. **A Lean proof** under `fw/proofs/<Name>.lean` (in-file `gen lean`/manual split,
   `lean`-checked) **only when the core invariant is provable in Lean core + omega** — noted
   per phase. Bind every method-call result to a local before passing it (call-boundary bug,
   `doc/08_tracking/bug/interp_method_call_result_as_arg_corruption_nested_2026-06-30.md`).

MDSOC discipline: new modules slot into the existing FIL/transport tiers, imports point
**downward only**, composition not inheritance, no shared mutable global, no `use std.ecs`
(driver tier). A new **transport** tier (DMA/PCIe regs) sits beside HIL; a new **fmc** tier
sits below FIL.

---

## P1 — Register-level Flash Memory Controller (FMC) model  *(G1)*  — ✅ DONE (2026-06-30)

> Landed: `fw/fil_fmc.spl` (`Fmc` register driver, owns the NAND device), `fil.spl` refactored to
> drive the NAND through the load→issue→read-result→ack handshake (behavior-preserving — the full
> 300-assertion suite + e2e mains stay green), `fil_fmc_selftest` in `test_fw`, and `proofs/Fmc.lean`
> (status state machine, gated in the system spec). The remaining `*_check.spl`/`doc/06_spec` items
> below were satisfied by folding the adversarial cases (sticky ERR, no-op-without-load) into
> `fil_fmc_selftest` rather than a separate runnable.

**Goal.** Replace direct `Fil`→`NandDevice` method calls with a register-MMIO handshake,
mirroring `fmc_driver.c`: a command/address/status register file; issue → poll → complete.

**Build.** `fw/fil_fmc.spl`: `FmcRegs{cmd, addr, len, status, data_ptr}` + `me fmc_issue(op, ppn)`
/ `me fmc_poll() -> i64` (BUSY/DONE/ERR bits). `NandDevice` becomes the device side of the bus.
`fil.spl` drives the NAND through `fil_fmc`, not direct calls.

**Tests.**
- `fil_fmc_selftest`: program/read/erase round-trip via the register handshake; status
  polling reaches DONE; injected fault sets the ERR bit and surfaces as a NAND fault.
- `fmc_check.spl`: back-to-back ops without status-clear must serialize correctly; ERR
  latch must not leak across ops.
- **Lean** (`Fmc.lean`): the issue→poll→done status state machine has no DONE-without-issue
  path and ERR is sticky until cleared (provable: small finite state machine).

**Silicon ceiling.** Real MMIO base addresses + ONFI NV-DDR timing are silicon; the register
**semantics** are faithful.

## P2 — Multi-channel / multi-way request scheduler  *(G2 — the largest real gap)*  — ✅ DONE (2026-06-30, additive)

> Landed **additive / behavior-preserving** (no PPN-geometry change, so the allocator/recovery/GC
> proofs + the 300-assertion suite stay green): `fw/fil_scheduler.spl` (`ChannelSched` over
> NUM_CHANNELS=8; `channel_of(blk) = blk mod 8` is a *derived view*). Per-channel serialization
> (one op per channel per step) + parallel drain (steps = deepest channel queue). Tested by
> `fil_scheduler_selftest` (`test_fw`) and `parallelism_check.spl` (8× striped speedup; unbalanced
> batch bounded by its deepest channel), the latter gated in the system spec. **No Lean proof** —
> the parallelism is a step-counting model (synchronous interpreter), proven by direct count, not
> ceremony. True channel-striped *allocation* (changing which PPN a write lands on) was
> deliberately **not** done: in a synchronous model it buys risk (re-deriving `Alloc.lean` on the
> ×8/call-boundary-prone band code) without real concurrency.

**Goal.** N channels × M ways operating in parallel, mirroring `low_level_scheduler.c`.

**Build.** `fw/fil_scheduler.spl`: per-channel ready/busy state, a per-(ch,way) request queue,
ready-based dispatch (never two ops on one die concurrently, independent dies overlap). FTL
band allocation becomes **channel-striped** so sequential writes spread across channels.
`fil` + `ftl_band` consume the scheduler.

**Tests.**
- `fil_scheduler_selftest`: enqueue across channels, assert independent dies advance in the
  same step and a busy die is never double-dispatched.
- `parallelism_check.spl`: a striped write batch completes in ≈ `ceil(n/channels)` steps
  (parallel speedup), not `n` (serial) — the property that justifies the gap.
- **Lean** (`Scheduler.lean`): mutual exclusion per die (no concurrent op on one (ch,way)) +
  progress (every queued request is eventually dispatched). Both provable in Lean core.

**Silicon ceiling.** Real per-channel NAND bus timing/contention is modeled as step counts,
not nanoseconds.

## P3 — Real ECC codec (BCH)  *(G3)* — PARTIAL WIRED FLOOR (2026-07-04)

> Landed floor: NAND now stores a compact SECDED ECC word in OOB/spare-area state at program time,
> the ONFI device and FMC latch that stored value on read, and `fil.read` decodes against it.
> A silent one-bit payload-window error is corrected before returning data, extending coverage beyond
> byte 0 through bit 16; double-bit payload corruption and stored-ECC/OOB metadata corruption fail
> closed. Covered by `ecc_check.spl` in the system spec. Full BCH/LDPC encode/decode remains open
> below.

**Goal.** Replace checksum+injected-flip with a real **BCH** codec: correct up to *t* bit
errors per codeword, detect beyond *t*.

**Build.** `fw/fil_ecc_bch.spl`: GF(2^m) arithmetic, syndrome compute, Berlekamp–Massey +
Chien search (or a bounded *t*=2 BCH for tractability). Keep `inject_read_bitflip` to drive it;
`fil.read` decodes through it.

**Tests.**
- `fil_ecc_bch_selftest`: encode→corrupt ≤t bits→decode recovers the word; >t bits →
  detected (NAND_ECC_FAIL), never silently mis-corrected.
- `ecc_bch_check.spl`: NIST/known BCH KAT vectors + a sweep over all single/double-flip
  positions (always corrected).
- **Lean** (`Ecc.lean`): start with the provable **Hamming SEC-DED** bound (single-error
  correct, double-error detect) as the formal floor; the full BCH bound is documented, not
  Lean-proven (Berlekamp–Massey is beyond Lean-core+omega).

**Silicon ceiling.** Commercial NAND uses hardware **LDPC** with soft-decision reads; BCH is a
faithful, partially-provable step, not the production code.

## P4 — DMA / host data transport (byte-accurate)  *(G4)* — PARTIAL WIRED FLOOR (2026-07-04)

> Landed floor: `hil_command.prp_byte` now decodes a compact two-segment PRP descriptor from
> `NvmeCmd.data`; both legacy HIL and the multi-queue NVMe controller write every LBA in
> `nblocks` from the modeled host segments, not just the first block. Covered by
> `host_transport_check.spl` in the system spec. Full HostMem/SGL/IOMMU descriptors remain open
> below.

**Goal.** Move real **bytes** between a modeled host memory and the device via a
PRP/SGL scatter-gather descriptor, replacing `i64`-value data.

**Build.** New **transport** tier `fw/dma.spl`: `HostMem{[u8]}`, `Prp{addr, len}` list,
`me dma_to_device(prp_list) -> [u8]` / `me dma_from_device(prp_list, bytes)`. `NvmeCmd` carries a
PRP pointer; `hil`/`nvme_controller` move data through DMA, not inline values.

**Tests.**
- `dma_selftest`: single- and multi-PRP scatter-gather round-trip; page-boundary split;
  partial/last-segment lengths.
- `dma_e2e_check.spl`: host writes a byte pattern → write cmd (DMA in) → read cmd (DMA out) →
  byte-exact match end-to-end.
- **Lean** (`Dma.lean`): a gather then scatter over the same PRP list is the identity on the
  byte range (provable: list/append algebra).

**Silicon ceiling.** Real PCIe BAR/doorbell electrical + IOMMU are modeled as a register file,
not silicon.

## P5 — DRAM-backed buffer & bounded map cache  *(G5)* — WIRED FLOOR (2026-07-04)

> Landed floor: `ftl_map` is already load-bearing in `Ftl` as a bounded LRU write-back map cache.
> Its capacity is tied to an explicit DRAM budget (`MAP_CACHE_DRAM_BUDGET_BYTES`), and the
> self-test proves dirty eviction and budget fit. `dram.spl` now adds a bounded DRAM arena span
> used by both HIL and the multi-queue controller before FTL programming; over-budget writes fail
> before any partial media update, and released spans are reusable (`dram_buffer_check.spl`).
> Real DRAM refresh/ECC/bandwidth remains open below.

**Goal.** A fixed DRAM budget backing the LRU write buffer + a bounded DFTL map cache with
miss→load-from-flash (real DRAM pressure), mirroring `lru_buffer.c`.

**Build.** `fw/dram.spl`: a sized `[u8]` arena + allocator (bump/free-list) with a hard
budget. `ftl_map` becomes a **bounded** cache (capacity from DRAM) with miss→flash-load +
LRU eviction of clean entries (dirty → flush first).

**Tests.**
- `dram_selftest`: alloc/free within budget; over-budget alloc fails cleanly (no overflow);
  LRU eviction order.
- `map_cache_check.spl`: working set > cache → correct values after evict+reload; a dirty
  entry is flushed before eviction (no lost mapping).
- **Lean**: cache-coherence invariant (a looked-up LBA returns its last written ppn whether
  cached or evicted) — provable as a map-equivalence lemma (extends `Recover.lean`'s model).

**Silicon ceiling.** Real DRAM refresh/ECC/bandwidth is not modeled.

## P6 — Concurrency: foreground I/O vs background tasks  *(G6)* — PARTIAL WIRED FLOOR (2026-07-04)

> Landed floor: `Firmware.service_tick()` processes at most one foreground HIL command and then
> one background GC opportunity. Both paths must acquire an explicit FTL-map owner token
> (`MAP_OWNER_FG`/`MAP_OWNER_BG`), and conflicts are counted instead of overlapping map access.
> Existing `service()` remains the drain API but now loops through `service_tick`, so the
> cooperative interleave is load-bearing. True multicore preemption/cache coherence remains open.

**Goal.** Model the commercial fg-I/O-vs-bg-task concurrency (GC/wear/scrub) sharing the FTL
map safely — the core "miniature-OS" challenge.

**Build.** Extend `firmware.service` into cooperative **tasks** (fg IO, bg GC, bg scrub) that
interleave per tick, each holding the FTL map only within an explicit critical section;
single-owner-per-mutable-resource (research §6 rule). No preemption (cooperative), so the
"lock" is a modeled ownership token.

**Tests.**
- `concurrency_selftest`: interleave a write stream with GC running; assert no lost write and
  no map corruption across the interleave.
- `race_check.spl`: a write to an LBA GC is concurrently relocating resolves to exactly one
  winner (newest), never a torn mapping.
- **Lean** (`Concurrency.lean`): single-writer mutual exclusion on the map ⇒ no interleaving
  produces a state unreachable by some serial order (serializability of the modeled tokens).

**Silicon ceiling.** True multi-core memory ordering / cache coherence is not modeled
(cooperative single-thread token model).

## P7 — Power states + thermal throttling  *(G7)*  — ✅ DONE + WIRED (2026-06-30)

> Landed: `fw/power_thermal.spl` — NVMe power states (Set/Get Features FEAT_POWER_MGMT, invalid
> rejected) + a Newtonian thermal model (heat ∝ activity scaled by power state, cooling ∝ excess
> over ambient → equilibrium under load, decay when idle) that latches a throttle over the
> threshold, raises the SMART critical-warning bit over the critical threshold, and counts
> AER-reportable throttle events. Tested by `power_thermal_selftest` (`test_fw`) and
> `thermal_check.spl` (sustained load → throttle + critical warning → cool-down recovery), the
> latter gated in the system spec. No Lean — a threshold model has no deeper falsifiable
> invariant. The heat/cool coefficients are an explicit calibration knob (real silicon needs
> measured tuning).
>
> **Wired into the live controller (2026-06-30).** `PowerThermal` is now a field on
> `NvmeController`: the live IO path (`process_one_io`) ticks it on every program/read (a write
> burns more energy than a read), and `do_get_log(LOG_SMART)` reports the model's live composite
> temperature and ORs its critical-warning bit into the SMART critical warning — replacing the
> old hardcoded `temperature: 313`. Two controller-selftest assertions prove the wiring: SMART
> temperature equals the live model's value, and a sustained write burst raises it above the idle
> baseline. The module is no longer a standalone shelf component — it is load-bearing.

**Goal.** NVMe power states (PSDs via Get/Set Features) + a thermal model that throttles
throughput over a threshold and reports composite temperature in SMART.

**Build.** `fw/power_thermal.spl`: temperature rises with op rate, decays when idle;
`throttle_factor()` caps dispatched ops/tick over `THERMAL_HIGH`; power-state transitions on
Set Features `FEAT_POWER_MGMT`. Wire composite temp + throttle events into SMART/AER.

**Tests.**
- `power_thermal_selftest`: power-state get/set round-trip; temp rises under load, throttle
  engages over threshold and releases below; SMART composite temp updates.
- `thermal_check.spl`: sustained load triggers a throttle AER event and a non-fatal temp
  warning, never a crash.

**Silicon ceiling.** No real sensor/voltage/clock — temperature is an activity model with a
calibration knob (`ponytail:` real sensors drift; leave the knob).

## P8 — Internal RAID/RAIN (die/channel failure protection)  *(G8)*  — ✅ DONE + WIRED (2026-06-30)

> Landed: `fw/rain.spl` (XOR parity stripe across the P2 channels; reconstruct a failed channel —
> data or parity — from the survivors), `rain_selftest` (`test_fw`), `rain_check.spl` (single-channel
> failure recovery, gated in the system spec), and `proofs/Rain.lean` — the **genuine** proof of
> the set: for any data and any survivor combination, reconstruction recovers the exact lost word
> (`parity = lost ⊕ s ⇒ parity ⊕ s = lost`), via Lean-core `Nat.xor` (would be false if the formula
> were wrong). Built on P2's channel model.
>
> **Wired into the live FTL (2026-06-30).** The physical address space is a clean
> NUM_GROUPS×NUM_CHANNELS block grid (`block = group·NUM_CHANNELS + channel`), so a RAIN stripe is
> one page per channel at a fixed (group, page). `Ftl` carries a per-stripe parity word array;
> writes/GC/format maintain `rain_parity` as physical pages change, `me.rain_seal()` remains a
> RAID parity-scrub/repair pass, and `me.rain_recover_channel(c)` rebuilds a corrupted/failed
> channel: per NAND block it computes the recovered payloads from live parity XOR the surviving
> channels, erases the failed block, and reprograms its live pages in place — the L2P ppns are
> unchanged, so the normal read path returns the original data. Proven end-to-end by
> `rain_ftl_check.spl` (256 known writes → a whole channel made uncorrectable, confirmed via
> `read_status` → rebuild without a pre-rebuild seal → every LBA reads back its original value)
> plus `ftl_rain_selftest` in `test_fw`.

**Goal.** XOR parity stripe across channels so a die/channel failure is recoverable.

**Build.** `fw/rain.spl`: per-stripe XOR parity (RAID5-like) across the P2 channels;
on an injected die/channel failure, reconstruct the lost page from the survivors + parity.

**Tests.**
- `rain_selftest`: write a stripe, inject a die failure, reconstruct, byte-exact recovery.
- `rain_check.spl`: a failure during GC relocation still reconstructs (no double fault on the
  parity path).
- **Lean** (`Rain.lean`): XOR reconstruction correctness — `p = a⊕b⊕c ⇒ a = p⊕b⊕c` — fully
  provable in Lean core (XOR group algebra), the strongest proof in the set.

**Silicon ceiling.** Real die/plane failure modes (partial-page, RBER drift) are modeled as
whole-unit erasure.

## P9 — Bare-metal rv32 no-alloc port  *(G9)*  — ◐ REFERENCE WIRED; FULL PORT REMAINS

> **Status (2026-07-07).** The fast direct-smoke path in
> `examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` is the small rv32 ELF recipe that
> avoids rebuilding the Rust seed and does not compile the full Simple firmware graph. QEMU boot
> evidence is valid only after `build/nvme_fw_rv32.elf` exists and prints
> `ALL RV32 NVME FW CHECKS PASS` / `RESULT: PASS`. `fw_rv32/entry.spl` remains a host-verified,
> array-free scalar reference for the Lean-proven RAIN reconstruction, SECDED ECC floor, fixed
> scheduler floor, fixed power/thermal floor, fixed map-cache floor, fixed band floor, fixed
> journal-ring floor, fixed HIL command/queue floor, fixed queue-phase floor, fixed task-pool
> fail-closed floor,
> io-opcode-read-zero-trim-flush floor, admin/format/fw-log floor, reactor floor,
> policy/target floor, DRAM/durability floor, wear/scrub floor, media-retire floor,
> power-cycle floor, backpressure/abort floor, feature-guard floor, and namespace-guard floor.
> That is useful P9 direct-smoke evidence, not the full firmware port. The full 22-module
> no-alloc firmware (`ftl_fill`/dict-map/journal-ring -> fixed-capacity) still has to replace the
> smoke path in the rv32 boot flow before P9 is complete.
>
> RV64 status (2026-07-07): `examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs`
> now mirrors the direct-smoke recipe and the RV64 SSpec is fail-closed on missing
> `build/nvme_fw_rv64.elf`. The current build attempt terminates before ELF output;
> see `doc/08_tracking/bug/nvme_fw_rv64_direct_build_timeout_2026-07-07.md`.

**Goal.** Port the FTL/HIL/FIL to `nogc_async_mut_noalloc` (no heap, fixed arrays, no `.push`)
and boot on `qemu-system-riscv32 -bios none`, joining the existing C NAND demo that already
boots ("ALL RV32 NAND CHECKS PASS", `BUILD_STATUS.md`).

**Build.** Replace `[i64]`/`.push` growth with fixed-capacity arrays sized at compile time;
move state into the no-alloc tier; a `simpleos_nvme_riscv32.elf` entry.

**Tests.**
- A QEMU rv32 **system test** under `test/03_system/os/qemu/` per
  `doc/07_guide/platform/simpleos/qemu_system_tests.md` (live boot, fail-closed, never
  `skip()`): boots, runs the FTL self-test on-device, prints "ALL RV32 NVME FW CHECKS PASS".
- Re-run every prior phase's `*_selftest` under the no-alloc build (parity with the host sim).

**Silicon ceiling.** QEMU rv32 is not an SSD SoC — no real NAND/PCIe peripherals; this proves
the firmware **logic** runs on a real ISA with no heap, the last step before an actual board.

---

## Sequencing & dependencies

```
P1 fmc ─► P2 scheduler ─► P8 rain (needs channels)
P3 ecc   (independent)
P4 dma   (independent) ─► P5 dram ─► P6 concurrency
P7 power/thermal (independent, after P2 for throttle hook)
P9 rv32  (LAST — no-alloc rewrite of P1–P8)
```

Highest value-per-effort first: **P1 (FMC) + P2 (scheduler)** close the biggest realism gap
(hardware bus + parallelism) and unlock P8; **P3 (BCH)** and **P8 (RAIN)** add the strongest
new proofs (Hamming bound, XOR reconstruction). P9 is the capstone.

## Definition of done (per phase) & overall ceiling

A phase is done when: module self-test green via `run`; its `*_check.spl` gated in the system
spec and `doc/06_spec` regenerated at 0 stubs; its Lean proof (where applicable) `lean`-green
with no `sorry`; `PRODUCTION_STATUS.md`/`README.md` updated; rebased + pushed. Even with all
nine phases complete the result is a **hardware-faithful, formally-anchored simulation**, not a
silicon-shippable binary — the honest ceiling this firmware has always stated.
