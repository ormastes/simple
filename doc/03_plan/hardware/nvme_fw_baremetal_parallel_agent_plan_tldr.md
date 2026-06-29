# NVMe FW Baremetal — Parallel-Agent Plan (TL;DR)

Build the `examples/09_embedded/simpleos_nvme_fw/` firmware with a **fleet of cheap workers
gated by Opus reviews**, following SPipe research→spec→implement→verify.

- **Haiku** = mechanical (sim, harness, crash-point specs, boilerplate, doc scaffolds).
- **Sonnet** = real module impl against a frozen interface (pool, queue, runtime, ftl, wal,
  recovery, gc, mapcache, offload, nvme-sim, hooks) — one disjoint file each.
- **Opus** = interface lock, Lean4 proofs, every review gate, accept/reject.

**Linchpin:** Phase L freezes shared names + invariants **before** any fan-out. Each wave =
parallel workers on disjoint files → an Opus gate barrier (correctness + false-green audit +
invariant + docs-freshness). Recovery (Wave 3) is a hard barrier. Compiler-bug-tail → file a
bug, take the simplest compiling form, never silent workaround.

Full plan: `nvme_fw_baremetal_parallel_agent_plan.md`.
Research: `doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`.

<!-- sdn-diagram:id=nvme_fw_plan_waves -->
```
Phase L (Opus, freeze) ─► Wave1 pool/queue+sim ─► Wave2 runtime+ftl ─► Wave3 WAL+P2L recovery
   │                          │ Lean A/B            │ Lean C/D          │ Lean E/F  (HARD barrier)
   └─ shared interfaces       ▼                     ▼                   ▼
      + invariants     [Opus gate]           [Opus gate]         [Opus gate] ─► Wave4 mapcache+gc
                                                                                 ▼ Lean G
        Wave6 hooks+validation+docs ◄─ Wave5 multicore+offload ◄────────────────┘ [Opus gate]
              │ Final Opus acceptance      │ Lean H
              ▼                            ▼
        green example + gated phases + readable doc/06_spec manuals
```
