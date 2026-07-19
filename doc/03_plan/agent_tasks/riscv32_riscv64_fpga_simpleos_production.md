# RV32/RV64 Simple-Generated FPGA CPU and Linux — Cooperative Task Plan

Date: 2026-07-18

## Research Sidecars

| Lane | Scope | Result | Merge status |
|---|---|---|---|
| `rv32_mmu_audit` | RV32 core/CSR/Sv32/PMP/generated evidence | Disconnected MMU/CSR, absent PMP, empty generated core, time-zero PASS | merged into local research |
| `rv64_mmu_audit` | RV64 core/CSR/Sv39/PMP/generated evidence | Partial state only; translation/CSR callers absent; identity LSU; empty generated core | merged into local research |
| `linux_fpga_audit` | bundle/Linux/login/FPGA/current-host evidence | Contract/synthetic smoke; no Linux/login/`ls`; current artifacts incomplete | merged into local research |

## Focused Design/Implementation Follow-up

| Lane | Scope | Result | Primary review |
|---|---|---|---|
| `rv32_mmu_audit` | canonical VHDL compiler boundary | Existing RV32 generated source has 13 real combinational `@hardware` helpers; canonical CLI/API and backend limits identified; RV64 still lacks an equivalent | accepted; Milestone 1 starts from this RV32 slice and does not claim a CPU |
| `rv64_mmu_audit` | SPipe/manual structure | Existing app/hardware feature lane, five-step visible flow, folded negative matrices, typed captures, and explicit failing helpers identified | accepted; helper names and spec path frozen by primary |
| `linux_fpga_audit` | smallest false-green removal | Keep bundle contract names but make CPU/testbench/formal execution fail with `GENERATED_RTL_NOT_IMPLEMENTED`; mark sidecars non-ready | accepted and implemented in Milestone 0 |
| `rv64_mmu_audit` | supervisor interrupt ownership and priority | Canonical `mie`/`mip`/`mideleg`, masked S aliases, independent PLIC M/S contexts, and strict software/external `SEIP` OR semantics | accepted; primary implemented and owns final review |
| `rv32_pmp_review` | canonical RV32 protection/privilege boundary | Move existing CSR/PMP owners into `CoreState`; gate Bare fetch/load/store once in `soc_tick`; add M/S/U stacks and delegated synchronous traps; keep interrupt/Sv32 controls WARL-zero until connected | reviewed during implementation; primary owns merge and final review |
| `rv32_pmp_review` | clocked Sv32 production seam | Reject direct `RamState` translation; port RV64 request/response ownership, preserve 34-bit PA, apply SUM/MXR/Svade, superpage-aware ASID/global TLB, and PMP-check PTE reads | accepted; walker implemented and reviewed |
| `rv32_pmp_review` | RV32 architectural memory frontend | Reuse RV64 transaction FSM; latch access context, sequence walker/final PMP/physical bus, preserve precise faults, and carry atomic/SC qualifiers | accepted; frontend implemented, reviewed, and integrated |
| `rv32_pmp_review` | RV32 clock-path integration | Make `CoreState` own RF/MMU/memory, connect SATP/SFENCE and cycle/retire counters, route one response-latched physical request through `soc_tick`, and prove a two-level translated fetch | accepted after legality, IALIGN, trap-stop, halt-drain, and FENCE corrections; primary owns commit |
| `rv32_pmp_review` | registered VHDL product boundary | Preserve `@clocked` in MIR, emit combinational `next_*` plus reset-aware output registers, reject generated nested clocks, and expose initialized RV32/RV64 roots | accepted after the four P1s and both reset closures passed focused static re-review; primary owns commit |
| `linux_buildroot_research` | official upstream producer baseline | Buildroot 2026.05.1, Linux 6.18.7, OpenSBI 1.6, blank-password root oracle, and stock hard-float/ext2 mismatch | accepted; primary derived tracked soft-float IMA/initramfs configs |
| `linux_media_audit` | shortest local producer and consumer path | Buildroot outputs and QEMU command identified; repo DT generator and media-address mismatches found | accepted; primary built and retained the strict RV32 media oracle |
| `dt_binding_audit` | canonical SoC/DT interrupt contract | RV32 has no PLIC route; shared bundle is RV32-only placeholder; separate RV64 peripherals are stubs; binding-complete phandles/contexts enumerated | accepted; product DT remains fail-closed pending hardware wiring |
| `rv32_linux_isa_audit` | canonical RV32 Linux readiness | Real Sv32/PMP/privilege path; missing M/A, S interrupts, PLIC, WFI, and counters | accepted; implementation order frozen |
| `rv32_m_impl` | iterative RV32M execution | 32-step radix-2 M unit, registered ready/RVFI phase, IMSU MISA, and focused core-path coverage | accepted after independent review PASS; primary owns merge |
| `rv32_a_design` | RV32A execution and retirement | Reuse the Sv32/PMP atomic frontend; add physical LR/SC reservation state, registered RVFI-ready retirement, exact AMO results, and one coherent-agent gate | accepted after independent high-capability review PASS; primary owns merge |
| `linux_media_audit` | RV32 supervisor interrupt and PLIC wiring | Port the proven RV64 CSR alias/delivery rules, reuse the shared two-context PLIC, route UART source 10, and derive binding-complete DT cells from that topology | design accepted; implementation is the next lane |

The collaboration runtime did not expose a Spark/lower-model selector. The
available sidecars were therefore kept read-only and bounded. Their conclusions
were reviewed against source by the primary normal/highest-capability model.

## Implementation Lanes After Selection

| Lane | Owned files | Deliverable | Merge dependency |
|---|---|---|---|
| Evidence hardening | current `check-riscv-*` wrappers and generated sidecar/spec | empty/constant/unconditional evidence fails | first |
| VHDL compiler | VHDL backend/driver and focused compiler specs | production core entries compile without fallback | evidence hardening |
| RV32 core | `rv32i_rtl`, RV32 MMU/PMP/CSR/trap tests | translated protected executable RV32 entity | VHDL compiler |
| RV64 core | `rv64gc_rtl`, RV64 MMU/PMP/CSR/trap tests | translated protected executable RV64 entity | VHDL compiler |
| SoC/Linux media | `soc_rtl`, profile/artifact manifest, OpenSBI/Linux/DT/rootfs | common pinned boot artifacts and QEMU oracle | RV32/RV64 interfaces frozen |
| RTL Linux | generated RTL simulator and SPipe spec/manual | login and `ls` per architecture | core + SoC/media |
| Formal/compliance | ACT4 profiles, RVFI/SBY, Lean/BYL constraints | non-vacuous per-architecture evidence | executable cores |
| KV260 | K26 DDR/terminal/constraints/build/program wrappers | physical RV32 and RV64 login/`ls` | RTL Linux |
| Docs/qualification | architecture, design, guide, manual, tracking/report | reviewed FPGA-language qualification | all lanes |

The immediate VHDL compiler gate is now executable in
`test/03_system/compiler/pure_simple_vhdl_source_of_truth_spec.spl`: compile
the tracked `core32_clocked` and `core64_clocked` roots, require their
registered `p_clk` boundary and translated MMU/PMP callees in the emitted
VHDL, then synthesize each entity with GHDL.
The contract bundle stays non-authoritative until both rows pass; packaging is
not a substitute for this gate.

## Shared Names

Reuse `RiscvMmuMode`, `RiscvLinuxProfile`, `RiscvPlatformProfile`, RV32
`MmuState`/`mmu_*`, RV64 `MmuState64`/`mmu64_*`, and
`RiscvFpgaProductProfile`. Do not create `RiscvLinuxProduct`; it does not exist.

Manual steps and checker policy are defined in
`doc/03_plan/sys_test/riscv32_riscv64_fpga_simpleos_production.md`.

## Ownership

- Merge owner: primary Codex `/root` lane.
- Generated-manual review owner: primary normal/highest-capability model.
- Final done-mark reviewer: primary normal/highest-capability model after all
  lower/sidecar findings are reconciled.
- Unrelated dirty worktree files remain owned by their existing sessions and
  must not enter this lane's commit.
