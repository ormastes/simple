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
  Lean4 (req 6), and sandboxed dynamic policy hooks (req 7: install gate, output clamps, modeled
  fuel bound).
- Out of scope (silicon-only — tracked, not built here): real BCH/Reed–Solomon hardware ECC,
  real register MMIO / PCIe transport, a persistent backing store, and multi-channel NAND
  timing. The bare-metal **rv32** no-alloc port remains the follow-up (see `BUILD_STATUS.md`).

## Acceptance bar (the goal is met when every box is checked) — ✅ MET

- [x] **No known data-loss or host-hang defect.** Each fixed with a regression test that
      fails before the fix and passes after (or, where the audit was wrong, verified a non-bug):
  - [x] GC never erases a victim block while any live page is un-relocated — alloc-fail aborts
        GC (`reclaim_block`/`gc_once`; `gc_safety_check.spl`, `ftl_gc_safety_selftest`).
  - [x] A fetched command **always** posts a completion — no host-hang. (Audit claim of a silent
        drop on pool exhaustion was **verified a non-bug**: `hil.tick`/`io_process` post a
        completion for every command, and the task-pool acquire→release within one synchronous
        tick, so it cannot exhaust.)
  - [x] Journal overflow is surfaced — `ensure_journal_room` forces a checkpoint+truncate before
        appending, never a silent ack of a lost record (`durability_check.spl` 600-write case).
  - [x] A write that cannot allocate fails atomically (`SC_NS_NOT_READY`, no half-applied
        map/journal state); the GC reserve keeps the device live (no write-cliff).
- [x] **Protocol surface.** Mandatory admin commands handled with correct `SC_*` — Identify,
      Get/Set Features, Create/Delete IO SQ/CQ, Get Log Page, **Abort, Async Event Request,
      Format NVM, Firmware Download/Commit**; IO: Read/Write/Flush/Trim. Unknown opcode →
      `SC_INVALID_OPCODE`; LBA/NLB out of range → `SC_LBA_RANGE` with **no integer overflow**
      (the overflow bypass that could index `l2p[]` out of range is fixed). Malformed input never
      crashes; negative-path tests at `cmd_validate` and the queue level. (NSID/reserved-field
      checks are N/A here: single-namespace device, no reserved fields modeled in `NvmeCmd`.)
- [x] **Durability.** A power cycle wipes *all* volatile DRAM state (write-back map cache + band
      valid bitmap); recovery replays the journal onto the flash-resident L2P, rebuilds the band
      bitmap, and re-applies the (persistent) bad-block table; committed writes survive, trims
      stay trimmed, retired blocks stay retired (`durability_check.spl`, `ftl_durability_selftest`).
- [x] **Media management.** Static wear-leveling (`wear_level_once`, erase-count-aware victim) and
      read-disturb scrubbing (`scrub_once`, per-block read counter) relocate data without loss
      (`wear_scrub_check.spl`, `ftl_media_mgmt_selftest`).
- [x] **Health.** SMART reflects real activity (data units r/w, host cmd counts, power cycles,
      unsafe shutdowns, media errors, percent-used from erase counts, available spare from bad
      blocks, critical warning); an error log records failed commands (`nvme_controller_selftest`).
- [x] **Formal (req 6).** `fw/proofs/{Alloc,Recover,Gc}.lean` prove the allocator/GC-reserve,
      committed-prefix recovery, and GC data-loss-guard invariants; each checks green with `lean`.
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

**Silicon boundary (unchanged, deferred).** Real BCH/Reed–Solomon hardware ECC (the sim keeps a
checksum + injected-bit-error model), real register MMIO / PCIe transport, a persistent backing
store, and multi-channel NAND timing remain out of scope; the bare-metal **rv32** no-alloc port is
the tracked follow-up (`BUILD_STATUS.md`). "Production level" here = production-grade *logic and
NVMe protocol compliance, simulation-validated*.

**Policy-hook sandbox boundary (req 7).** The real silicon trust boundary for dynamically loaded
policy code is cryptographic module signing + a static verifier; in-sim the boundary is the
**install gate** (only the four policy kinds load; metadata/recovery/commit domains are rejected),
**structural isolation** (a hook is a pure function of copied scalars with no FTL / NAND / journal
handle), and **output validation** (clamps; the GC hook only scores trusted CLOSED candidates, so
the chosen victim is always CLOSED — proven in `fw/proofs/Hooks.lean`). The per-invocation **fuel
bound is *modeled*** — a cooperative self-reported budget that discards over-budget votes, not a
hard preemption — so it is a liveness/QoS guard, not the safety claim.
