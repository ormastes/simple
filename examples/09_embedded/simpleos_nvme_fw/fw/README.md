# SimpleOS NVMe SSD firmware (`fw/`)

A bare-metal **NVMe SSD controller firmware**, written in pure Simple as a host-runnable
**simulation** of the full data path: host NVMe queues → translation layer → flash media.
Built layer-by-layer with parallel agents (Sonnet builders + Opus review gates), gated by
`bin/simple run` self-tests (the `check` typecheck path is avoided — see `CONVENTIONS.md`).

> Simulation only — no hardware, no QEMU, no real MMIO. The geometry (4 planes × 16 blocks ×
> 64 pages = 4096 pages, 3072 surfaced LBAs) and a one-byte-per-page payload stand in for a
> real device so the entire stack runs and self-verifies on the host.

## Run it

```bash
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/sim_main.spl   # single-queue end-to-end demo
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/test_fw.spl    # full self-test suite (300 checks)
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/nvme_main.spl  # NVMe admin/multi-IO-queue controller e2e
```

Standalone production-hardening regressions and proofs:

```bash
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/gc_safety_check.spl   # GC data-loss guard + no write-cliff
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/durability_check.spl  # power-loss recovery + WAL overflow
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/wear_scrub_check.spl  # static wear-leveling + read-disturb scrub
lean examples/09_embedded/simpleos_nvme_fw/fw/proofs/Alloc.lean              # + Recover.lean, Gc.lean (req 6)
```

> **Production-hardening status & acceptance bar:** `fw/PRODUCTION_STATUS.md` — production-grade
> *logic and NVMe protocol compliance, simulation-validated* (the silicon boundary is stated there).
>
> Operator guide (both `fw/` firmware and the sibling `emu/` emulator):
> `doc/07_guide/hardware/nvme_firmware/`.

`sim_main` drives a full workload: 128 writes → read-back → overwrite-all (write
amplification) → **garbage collection** (reclaim stale blocks, logical view preserved) →
trim → **power-fail + recovery** (committed state survives, trim stays trimmed).

## Architecture (MDSOC+ : layered domains)

```
            host NVMe SQ/CQ rings
                    │
   HIL  ┌───────────▼───────────┐   hil_queue · hil_command · fw_pool · hil
        │ fetch → validate →    │   (decode, generation-handle task context,
        │ dispatch → complete   │    SQ→CQ reactor)
        └───────────┬───────────┘
   FTL  ┌───────────▼───────────┐   ftl_map (DFTL write-back cache) · ftl_band
        │ L2P map · log alloc · │   (log-structured allocator + valid bitmap) ·
        │ WAL · GC · recovery   │   ftl_journal (WAL+checkpoint+A/B superblock) ·
        └───────────┬───────────┘   ftl_gc (greedy victim) · ftl (write/read/trim/recover)
   FIL  ┌───────────▼───────────┐   fil_nand (sim NAND + OOB) · fil_ecc · fil_badblock
        │ program/read/erase +  │   · fil (ECC-verified reads, bad-block retirement)
        │ ECC + bad-block remap │
        └───────────────────────┘
   firmware.spl — cooperative reactor wrapping the stack (service cycle = drain queues +
   background GC below the free-block watermark; checkpoint; power-cycle).
```

## Module map

| Layer | Modules |
|-------|---------|
| Interface | `nvme_types` (constants, `Handle`, `NvmeCmd`/`NvmeCpl`, geometry, helpers) |
| **FIL** | `fil_nand`, `fil_nand_device` (ONFI NAND *device*, now driving the FIL), `fil_ecc`, `fil_badblock`, `fil` |
| **FTL** | `ftl_map`, `ftl_band`, `ftl_journal`, `ftl_gc`, `ftl` |
| **HIL + core** | `hil_queue`, `hil_command`, `fw_pool`, `hil`, `firmware` |
| **NVMe controller front end** | `nvme_admin_types`, `nvme_admin` (admin queue: Identify, Create/Delete IO SQ/CQ, Get/Set Features, Get Log Page), `nvme_qset` (multi IO queue, round-robin), `nvme_controller` |
| Tests | `test_fw` (all self-tests, 300 checks), `sim_main` (single-queue e2e), `nvme_main` (controller e2e) |

## Requirements coverage (from the research report)

| # | Requirement | Where |
|---|-------------|-------|
| 1 | Coroutine / cooperative tasks | `firmware.service()` reactor; `fw_pool` write-task state machine driven by `hil.tick()` |
| 2 | State-machine memory vars over locals | task phase (`PH_*`) held in the `fw_pool` slot (task context), not call-stack locals |
| 3 | Index pointer + object pool | `fw_pool` generation-checked `Handle{pool,index,generation}` (use-after-free guard) |
| 4 | MDSOC+ multi-domain architecture | HIL / FTL / FIL domains, composed structs (`Firmware{hil{ftl{fil}}}`) |
| 5 | Offloadable operations | `fil` offload-op seam (ECC is a swappable op); abstract page-level API |
| 6 | Lean4 formal verification | **done** — `fw/proofs/{Alloc,Recover,Gc}.lean` prove the allocator/GC-reserve, committed-prefix recovery, and GC data-loss-guard invariants (standalone, `lean`-checked, no mechanical link to executed bytes). The sibling **`emu/`** has its own proofs (`emu/proofs/*.lean`) |
| 7 | Dynamic loaded code hooks | **planned** (sandboxed GC/QoS policy hooks) per the plan |

Recovery and verification are architectural (committed-prefix recovery is proven by the
crash/recover self-tests and `sim_main`), per the report's central recommendation. Research +
build plan: `doc/01_research/hardware/nvme_firmware/` and
`doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md`.
