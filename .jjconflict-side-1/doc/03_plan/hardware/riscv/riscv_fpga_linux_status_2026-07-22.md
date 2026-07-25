# RISC-V FPGA/Linux + JTAG — Consolidated Status (2026-07-22, Lane V audit)

**Verified against origin tip `ddb8ebc8090`, re-checked at `3b36b68cd11`
(Lane M, new tip)** (every row content-grepped or
`git ls-tree`/`merge-base`-checked in a clean worktree of FETCH_HEAD; no claim
below rests on a plan doc alone). Companion plans:
`riscv_unification_parallel_agent_plan_2026-07-21.md`,
`../debug/riscv_jtag_debug_plan_2026-07-21.md`.

All claimed session commits are ancestors of the origin tip: `61fb4f0d884`,
`be5f80c81a0`, `46c54a743d0`, `e0d8fb67e58`, `c7cd8f01450`, `81d904de4b5`,
`b952c456076`, `a6723de99a5`, `5ee6cebc41e`, `c95684a1862`, `801109c06ba`,
`355fdf4ead0`, `f6a691ca9f7`, `a318432b214`, `8e8d8d8117b`, `13e91fe718b`,
`483b213e4e1`, `41f6fa7454d`. (Local-only `a9a344e96a3` is NOT on origin; its
content was relanded via `46c54a743d0` — verified: c.add/c.jalr rs2
discrimination at `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd:651`.)

## Section 1 — Linux-on-FPGA

| Deliverable | Status | Evidence | Remaining |
|---|---|---|---|
| W1-A honest FPGA profiles | DONE (superseded) | `61fb4f0d884` then `37cf118af5c`; tip strings are `rv32imc_zicsr`/`rv64imc_zicsr` + soft-float `ilp32`/`lp64` in `src/lib/hardware/fpga_linux/riscv_fpga_linux.spl` (hard-float-requires-F rule kept). Plan doc's claimed strings `rv32imac_zicsr_zifencei` are NOT at tip — corrected, intent intact | Re-run fpga_linux spec after self-hosted redeploy (runner hang) |
| W1-B RTL truth checker | DONE (not gating) | `scripts/check/check-riscv-rtl-truth.shs` present; correctly RED on real finding | Wire into pre-commit only after soc_top_rv64 bug resolved |
| rv32 PL core proven (c.add, divider, putint) | DONE (sim) | reland `46c54a743d0`; c.add/c.jalr fix at `rv32_exec_core.vhd:651`; GHDL boot→login→ls→TEST PASSED (re-run bit-identical under `41f6fa7454d`) | Board serial proof |
| rv64 core64 unblocked in-tree | DONE | `b952c456076`: 0 `@hardware` in `rv64gc_rtl/core.spl`, `is_csr` in `decode.spl`, dead `core64_cycle` removed | Honest re-land of memory_access/PMP path |
| W2-D soc_top_64 real-core wiring | DONE | `soc_top_64.spl`: 12 refs `core64_combinational`/`core64_update`; PC+4 bypass gone | SSpec gate blocked by deployed-runner hang (probe-only evidence) |
| RV64 bootrom (RV32-encoding sext fix) | DONE | `5ee6cebc41e`+`c95684a1862`; `bootrom_read64` wired (`soc_top_64.spl`:3 refs, `bootrom.spl`:2); bug doc `soc64_bootrom_rv32_encoded_sext_misjump` FIXED — consistent | — |
| soc64 MMIO: CLINT + UART16550 TX | DONE | `a6723de99a5`; 29 uart refs + mtip/msip in `soc_top_64.spl` | UART IIR/FCR/DLAB; RX side beyond claim/complete |
| RV64 Linux-path: timer + external irq + wfi/A-ext | DONE (M-mode) | `8e8d8d8117b`, `13e91fe718b`, `483b213e4e1`; verified: wfi in `core.spl` (9), LR/SC+AMO in `atomics.spl`, PLIC→MEIP wired | misalign/illegal-AMO exceptions, UART IIR/FCR/DLAB |
| RV64 S-mode subset + delegation (Lane M) | DONE (subset) | `3b36b68cd11` (verified ancestor + content: medeleg/mideleg delegation-aware trap take in `trap.spl`, S-CSRs sstatus/sie/sip/stvec/sepc/scause/satp, sret, PLIC ctx1→SEIP in `plic.spl`/`soc_top_64.spl`; also fixed real bug — `trap64_enter` computed then DROPPED delegated S-CSR writes; probes 83/0 PASS) | Sv39 activation (mmu_sv39.spl exists, fetch/data translation unwired), page-fault causes + stval, SBI timer/STIP, full sstatus view, OpenSBI payload run |
| First K26 bitstream + board program | DONE (bitstream) / BLOCKED (board proof) | `41f6fa7454d`: BRAM banking rom_a/rom_b in `rv32_exec_core.vhd` (+308 lines); board-program log is untracked `build/…` (unverifiable from origin — claim-only) | UART capture = 0 bytes: needs 3v3 PMOD UART adapter + timing fix below |
| K26 timing closure | BLOCKED (OPEN bug) | `k26_rv32_no_timing_constraints_wns_neg17_2026-07-22.md`: flow effectively unconstrained (routed report "no user specified timing constraints" despite a `create_clock` line in `build_k26_rv32.shs:54` — evidently not taking effect on cfgmclk), WNS −17.1 ns @100 MHz probe, max ≈36.9 MHz, baud divisor mismatch | Constrain real clock, re-close timing or lower CLK_FREQ + baud recompute |
| rv64 FPGA synthesis top | BLOCKED (OPEN bug) | `rv64_smoke_tb_dangling_soc_top_rv64_entity_2026-07-21.md` open + confirmed: no `entity soc_top_rv64` anywhere tracked; tb + `build_k26_rv64.shs` + wrapper reference it | Define/generate the entity or repoint consumers |
| rv64gc_rtl package hygiene | OPEN | `rv64gc_rtl/__init__.spl:48` exports `core64_step`; zero definitions tree-wide (bug `rv64gc_core64_step_removed_dangling_export` still open; NOT fixed by `b952c456076`) | Remove export or reintroduce shim |
| SimpleOS kernels via native codegen | BLOCKED (compiler) | `riscv64_kernel_codegen_blocker_2026-07-20.md`, `riscv32_cranelift_emission_blocker_2026-07-20.md` — both open, no status change found at tip | rv64 MIR/codegen fixes; rv32 emission path |
| Spec-suite debt | OPEN | `rv64_compliance_spec_missing_core_ext_pkg_modules`, `rv64_memory_ops_spec_missing_rv64ram`, `generate_rv64_test_program_package_missing_impl` all confirmed still real (`src/lib/hardware/rv64gc/` has only `__init__/mod/top`; `src/hardware/fpga_linux/` lacks the generator) | Implement or retire the specs |
| Gate infrastructure | DEGRADED | deployed-seed SSpec runner hang (`deployed_seed_test_runner_init_hang_2026-07-17.md`) masks every spec gate; all recent evidence is standalone probes | Self-hosted redeploy, then re-run all named gates |

## Section 2 — JTAG (RISC-V Debug v0.13)

| Deliverable | Status | Evidence | Remaining |
|---|---|---|---|
| Stage 1 TAP/DTM/DMI | DONE | `e0d8fb67e58`; `jtag_tap.vhd`, `riscv_dtm.vhd`, `dmi_bus.vhd`, `tb_jtag_dtm_dmi.vhd` all at `src/lib/hardware/debug/`; GHDL 5/5 | CDC at hart integration |
| Stage 2 Debug Module halt/resume | DONE | `c7cd8f01450`; `riscv_debug_module.vhd`, `debug_registers.vhd`, `tb_debug_module.vhd` present | Hart ports are stubs |
| Stage 3 abstract commands/GPR | DONE | `801109c06ba`; `tb_abstract_cmds.vhd` present, 7/7 + regressions | — |
| Stage 4 dpc/dcsr single-step | DONE | `355fdf4ead0`; `tb_debug_csrs.vhd` present, 6/6 | — |
| Stage 5 SBA + live OpenOCD attach | DONE | `f6a691ca9f7`; `sba_test_mem.vhd`, `tb_sba.vhd`, `openocd_bitbang_glue.c`, `tb_openocd_bitbang.vhd`, `openocd_riscv_sim.cfg`, transcript `openocd_attach.md` all in-tree; OpenOCD 0.12.0 TAP 0x15350067, halt/step/resume rc=0 | — |
| AOP hart debug hooks | DONE (seams only) | `a318432b214`; `src/lib/hardware/debug_hooks/` (3 files); 2 compiler AOP gaps filed (`aop_hart_hooks_weaving_gaps_2026-07-22`) | Compiler weaving gaps: entry-module-only run path; execution(...) predicate matcher |
| Hart integration (real cores) | NOT STARTED (BRAM-gated) | Plan item 7; DM drives a tb fake hart; DM CSRs are stubs | haltreq/resumereq/GPR-ack into real rv32/rv64 cores; real CSR file; sb_* onto SoC bus w/ arbitration |
| GDB end-to-end on :3333 | IN-FLIGHT | Lane U (this wave): gdb script + procedure against the tb fake hart | Live GDB blocked if no riscv gdb binary on host; then re-run against real hart |
| KV260 JTAG observability | OPEN | `kv260_naxriscv_bitstream_no_jtag_observability.md` still Open | On-board debug requires hart integration + FPGA JTAG routing |

## Honest critical path

**To Linux-on-FPGA (rv64, QEMU-grade first, then board):**
1. Sv39 activation (wire `mmu_sv39.spl` into fetch/data), page-fault causes +
   stval, SBI timer/STIP, full sstatus view →
   **OpenSBI payload run on soc_top_64 in simulation** (S-mode delegation +
   PLIC ctx1/SEIP landed `3b36b68cd11`; nothing Linux-shaped has executed yet —
   everything to date is bare probes).
2. Define the rv64 synthesis top (`soc_top_rv64` dangling-entity bug) so the
   rv64 SoC can synthesize at all.
3. K26 timing closure (constraint takes effect + WNS ≥ 0 at chosen clock, baud
   recomputed) — currently ~36.9 MHz max vs 100 MHz assumption.
4. Physical serial proof: 3v3 PMOD UART adapter at H12/E10; the board has only
   been *programmed* (DONE=HIGH), never *observed*. Per board-runnable rule,
   QEMU/GHDL-only remains a defect until this lands.
5. Re-run all spec gates once the deployed-runner hang is cleared — probe-only
   evidence is currently the norm, not the exception.

**To JTAG-done:**
1. Hart integration (the single remaining plan item): wire
   haltreq/resumereq/halted/running + GPR ack + dpc/step/prv into the real
   rv32/rv64 cores, replace DM stub CSRs, arbitrate sb_* onto the SoC bus —
   gated on BRAM stability (BRAM banking landed `41f6fa7454d`, so the gate
   condition is now satisfiable).
2. GDB-over-OpenOCD e2e on :3333 against the real hart (Lane U's fake-hart
   harness is the stepping stone).
3. On-board attach via KV260 JTAG once hart integration + timing closure land.

## Claims that FAILED or were corrected by this audit

1. **W1-A profile strings**: plan doc claims `rv32imac_zicsr_zifencei`/
   `rv64imac_zicsr_zifencei`; tip has `rv32imc_zicsr`/`rv64imc_zicsr`
   (superseded by `37cf118af5c`). Honest-profile intent verified; exact claim
   stale.
2. **`core64_step` dangling export still live**: `rv64gc_rtl/__init__.spl:48`
   exports a function with zero definitions tree-wide. The "core64 UNBLOCKED"
   fix (`b952c456076`) did NOT resolve this bug; its doc is correctly open.
3. **Board evidence is claim-only**: the KV260 program log lives under
   untracked `build/`; nothing on origin proves the board program. UART capture
   was 0 bytes — no board serial proof exists.
4. **"Lane E/I/L" claims**: no such lane names exist in any in-tree RISC-V
   plan doc — unverifiable as stated (coordinator-side naming; the in-tree
   record uses W-lanes + JTAG stages).
5. **`create_clock` ambiguity**: `build_k26_rv32.shs:54` contains
   `create_clock … cfgmclk`, yet the routed report says no user constraints —
   the OPEN timing bug is real; the constraint evidently never attaches.

## Recommended plan-doc corrections (not applied — audit is docs-read-only per coordinator)

For `riscv_unification_parallel_agent_plan_2026-07-21.md`:
- W1-A bullet: annotate that the claimed profile strings were superseded by
  `37cf118af5c` (`rv32imc_zicsr`/`rv64imc_zicsr`, soft-float `ilp32`/`lp64`);
  the `rv32imac_zicsr_zifencei` strings no longer exist at tip.
- W2-C bullet: the dangling `core64_step` export is STILL unresolved at
  `3b36b68cd11` (`rv64gc_rtl/__init__.spl` exports it; zero definitions
  tree-wide) — `b952c456076` did not close it; the bug doc remains open.
- Session update 3, K26 entry: mark the board program as claim-only (evidence
  log untracked under `build/`), and note board serial remains unproven
  (0 UART bytes; PMOD adapter + timing bug both outstanding).
- Session update 3, "Remaining for OpenSBI/Linux": S-mode + delegation and
  PLIC ctx1/SEIP are now DONE (`3b36b68cd11`); remaining list should read:
  Sv39 activation, page-fault causes + stval, SBI timer/STIP, full sstatus
  view, misalign/illegal-AMO, UART IIR/FCR/DLAB, OpenSBI payload run.

For `../debug/riscv_jtag_debug_plan_2026-07-21.md`:
- Header `**Status**: PLANNED` is stale — should read: Stages 1–5 LANDED
  (files verified at tip), only hart integration remains, and the BRAM gate
  is now satisfiable (`41f6fa7454d` BRAM banking landed).
