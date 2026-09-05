# NVMe SSD Firmware Architecture (TL;DR)

**Thesis:** start simple and verifiable, not clever. Bare-metal/simple-OS cooperative
**coroutine** firmware + bounded **object pools** + **generation handles** + **band/log-structured
page FTL** + **DFTL** map cache + **checkpoint/WAL/P2L** recovery + incremental **Lean4** model proofs.

- **Runtime:** SPDK-style poll-mode reactor, not a preemptive RTOS. No blocking in tasks; ISRs only enqueue.
- **State:** lives in task-context objects (state machine), not call-stack locals → traceable/recoverable.
- **Handles:** `{pool,index,generation}` over raw pointers → no use-after-free across yield.
- **FTL:** band-based log-structured page mapping; RAM holds hot L2P + active-band state; flash holds
  checkpoints, map pages, per-band P2L, valid maps, journal.
- **Recovery (the heart):** superblock A/B → latest checkpoint → WAL replay → P2L scan by sequence id.
  Prove `recover(crash(trace)) = committed_prefix(trace)`. Crash-inject after every metadata step.
- **Offload:** abstract ops (CRC/ECC/XOR/bitmap/DMA) with a software fallback for each.
- **Dynamic code:** only sandboxed, bounded, signed policy hooks (GC score, QoS, hot/cold); never WAL/
  checkpoint/superblock/bad-block.
- **Verify:** Lean4 model-first (pool, queue, coroutine protocol, recovery, P2L/L2P, GC, multicore) —
  models/protocols, not the whole binary. Proof style from FSCQ / Crash Hoare Logic.

Full report: `nvme_ssd_firmware_architecture.md`. Corrections/extensions: `research_addendum_2026-06-29.md`.
Build plan: `doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md`.

<!-- sdn-diagram:id=nvme_fw_stack -->
```
NVMe queues → coroutine runtime → verified pools/queues → FTL task graph
  → band/log-structured mapping → checkpoint+WAL+P2L recovery → NAND scheduler
  → optional controller offload → sandboxed dynamic policy hooks
```
