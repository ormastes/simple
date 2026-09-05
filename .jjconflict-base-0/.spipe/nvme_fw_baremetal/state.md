# Feature: nvme_fw_baremetal

## Raw Request
> use spipe dev skill, make example submodule on github about nvme fw baremetal dev
> which base part of simple os baremetal (minimum uses). see next and make more research,
> and detail plan for parallel agents with smaller sonnet and haiku agents with opus reviews.
> make more research and detail plan >> check last research doc

(Driven by the NVMe SSD Firmware Architecture research report captured at
`doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`.)

## Task Type
feature

## Refined Goal
Stand up a minimal, host-runnable bare-metal NVMe SSD firmware **example** under
`examples/09_embedded/simpleos_nvme_fw/` that reuses SimpleOS baremetal primitives minimally,
plus the research doc and a parallel-agent build plan (Haiku/Sonnet workers gated by Opus
reviews) that grows the example along the research roadmap.

## Acceptance Criteria
- AC-1: `doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md` exists and
  captures the research report; factual claims validated/extended in `research_addendum_2026-06-29.md`.
- AC-2: `examples/09_embedded/simpleos_nvme_fw/` contains a minimal pure-Simple example
  (`main.spl` = log-structured FTL + P2L/OOB-scan crash recovery + offload seam;
  `pool_demo.spl` = generation-handle pool + cooperative phase state machine) that
  `bin/simple run` exits 0 with REAL assertions (no `expect(true)`), demonstrating:
  generation-handle object pool, state-machine task phases, simulated NAND, and
  crash→recover-committed-state over a tiny log-structured FTL. **`run` is the deterministic
  verification gate**; `bin/simple check` is blocked by a filed compiler bug
  (`doc/08_tracking/bug/sspec_simple_check_superlinear_two_impls_2026-06-29.md`) — a
  non-deterministic typecheck-blowup on array-field structs with several `me` methods.
- AC-3: The example is "minimum uses" — one coherent slice, in-memory simulation only (no QEMU,
  no real MMIO/hardware), reusing existing std primitives where a few lines won't do.
- AC-4: `doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md` maps roadmap phases 0–11
  to disjoint Haiku/Sonnet work units, each behind an Opus review gate, with a frozen interface-lock
  pass before any worker fan-out and a parallel Lean4 verification track.
- AC-5 (docs-freshness): generated `doc/06_spec` manuals for any spec added read as operator manuals
  with `0 stubs`; new docs carry a `*_tldr.md` (≤30 lines + ≥1 SDN diagram). Checked at final verify.

## Scope Exclusions
- NOT building the full 11-phase firmware this lane — only the Phase-1 minimal slice + the plan.
- NO real hardware / QEMU / NVMe device I/O; NO literal git submodule (separate GitHub repo) —
  the example lives in-repo (committed to GitHub via the main repo). Promote to a standalone
  submodule only if the user later asks.
- NO Lean4 proofs authored this lane (the plan schedules them; none are an AC here).

## Cooperative Review
Full plan: `doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md`.

- **Lower-model sidecars:** Claude **Haiku** (simulator fixtures, trace/crash-injection harness,
  repetitive crash-point specs, boilerplate, generated-manual scaffolding) and Claude **Sonnet**
  (real module implementation: pool, queue, runtime, ftl, wal, recovery, gc, mapcache, offload,
  nvme sim, hooks — one disjoint file each).
- **Merge owner:** Opus. **Final reviewer:** Opus (adversarial; false-green audit + invariant check).
- **Shared interface names (to freeze in Phase L):** `Handle{index,generation}`, `WriteTask`,
  `ReadTask`, `SimNand`, `Wal`, `WalRecord{kind,lba,old_ppn,new_ppn,seq}`, `Ftl`, `OffloadOps`,
  `Checkpoint`, `Superblock`, `BandState`, `MapCacheEntry`, `GcTask`.
- **Manual `step("...")` flow helpers:** `step("write LBA")`, `step("read back")`,
  `step("overwrite")`, `step("simulate crash")`, `step("recover")`, `step("verify committed state")`.
- **Setup/checker helpers:** `make_ftl()`, `crash_clear_l2p(ftl)`, `expect_read(ftl, lba, want)`.
- **Fail-fast placeholders:** unbuilt helpers are `fail("TODO: <name>")` / `assert(false, ...)` —
  never silent stubs.
- **Generated-manual review owner:** Opus (docs-freshness gate at final verify).

## Phase
dev-done

## Log
- dev: Created lane; 5 acceptance criteria (type: feature). Research report saved as canonical
  research doc; parallel-agent plan authored. Research-extend workflow (Haiku/Sonnet workers +
  Opus verify/synthesis) and the Phase-1 scaffold agent launched in background.
- research: Workflow returned addendum (40 sources, 16 adversarial verdicts, 14 corrections);
  verified corrections folded into the main report (NVMe spec family/transports/rev 2.3, SPDK
  lock-free I/O path, chunk/zone FTL metadata, FSCQ=Coq, LightNVM removed in Linux 5.15).
- spec/impl: Phase-1 example built and `bin/simple run`-green (main.spl 7/7, pool_demo 4/4, real
  assertions). Hit a real compiler bug — `bin/simple check` non-deterministically hangs/crashes on
  array-field structs with ≥3 `me` methods; filed the bug, split into two lean files, kept the
  natural form (no silent workaround), documented `run` as the gate in README + state.
