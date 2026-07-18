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
| `rv32_pmp_review` | RV32 architectural memory frontend | Reuse RV64 transaction FSM; latch access context, sequence walker/final PMP/physical bus, preserve precise faults, and carry atomic/SC qualifiers | accepted; frontend implemented and reviewed; `soc_tick` follows |

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
