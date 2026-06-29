# NVMe firmware — production-hardening status & acceptance bar

**Scope (read this first).** This firmware is a **host-runnable simulation** of an NVMe SSD
controller, written in pure Simple. "Production level" here means **production-grade *logic*
and **NVMe protocol compliance**, validated in simulation** — *not* a binary shippable to
silicon. The simulation boundary is deliberate and unchanged:

- In scope (verified here): data-path correctness (no data-loss / host-hang defects), the
  mandatory NVMe admin + IO command surface with correct completion status codes, malformed
  input never crashing the controller, power-loss recovery as a real property (volatile state
  wiped, L2P + bad-block table rebuilt from NAND), wear-leveling + read-disturb-scrub *logic*,
  SMART/health telemetry wired to real activity, and the safety-critical invariants proven in
  Lean4 (req 6).
- Out of scope (silicon-only — tracked, not built here): real BCH/Reed–Solomon hardware ECC,
  real register MMIO / PCIe transport, a persistent backing store, and multi-channel NAND
  timing. The bare-metal **rv32** no-alloc port remains the follow-up (see `BUILD_STATUS.md`).

## Acceptance bar (the goal is met when every box is checked)

- [ ] **No known data-loss or host-hang defect.** Each fixed with a regression test that
      fails before the fix and passes after:
  - [ ] GC never erases a victim block while any live page is un-relocated (alloc-fail aborts GC).
  - [ ] A command that cannot be admitted (pool/queue exhausted) returns a completion to the
        host (`SC_QUEUE_FULL`) — it never silently vanishes.
  - [ ] Journal overflow is surfaced (forces a checkpoint), never a silent ack of a lost record.
  - [ ] A write that cannot allocate fails atomically (no half-applied map/journal state).
- [ ] **Protocol surface.** All mandatory admin + IO commands handled with correct `SC_*`;
      unknown opcode → `SC_INVALID_OPCODE`; bad nsid → `SC_INVALID_NS`; LBA/NLB out of range →
      `SC_LBA_OUT_OF_RANGE` with no integer overflow; reserved-field misuse → `SC_INVALID_FIELD`.
      Malformed input never crashes. Negative-path tests for each.
- [ ] **Durability.** A power cycle wipes *all* volatile state (L2P map, band bitmap, BBT, WAL);
      recovery rebuilds L2P and the bad-block table from NAND; committed writes survive, trims
      stay trimmed, retired blocks stay retired. Proven by test.
- [ ] **Media management.** Static wear-leveling (erase-count-aware victim/relocation) and
      read-disturb scrubbing logic exercised by tests.
- [ ] **Health.** SMART reflects real activity (data units r/w, host cmd counts, power cycles,
      unsafe shutdowns, media errors, percentage used, available spare, max erase count); an
      error log records failed commands.
- [ ] **Formal (req 6).** `fw/proofs/*.lean` prove the safety-critical FTL invariants and check
      green with `lean`.
- [ ] **Green + documented.** `test_fw`, `sim_main`, `nvme_main` and the production self-tests
      pass via `bin/simple run`; the sspec tiers pass via `bin/simple test`; `doc/06_spec`
      regenerated at 0 stubs; this doc + `README`/`BUILD_STATUS` state the silicon boundary.

Progress is tracked by checking boxes above as each lands (committed, run-green).
