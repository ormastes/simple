<!-- codex-research -->
# VHDL Backend + Linux RTL Local Research

Scope: determine whether Simple currently generates real VHDL/RTL for a RISC-V CPU/SoC that can boot Linux, and list fixes needed.

## Current Reality

| Area | Evidence | Status |
|---|---|---|
| MIR-to-VHDL backend | `src/compiler/70.backend/backend/vhdl_backend.spl` emits packages, entities, ports, signals, constants, simple ops, and some VHDL-specific MIR instructions. | Partial backend implementation. |
| VHDL builder API | `src/compiler/70.backend/backend/vhdl/vhdl_builder.spl` plus `examples/09_embedded/vhdl/builder/*`. | Useful manual VHDL text builder, not proof of backend lowering. |
| Backend-generated examples | `examples/09_embedded/vhdl/README.md` states `backend/` is pending/empty and needs completion of backend phases 3-4. | Not proven. |
| RV32 VHDL CPU | `examples/09_embedded/fpga_riscv/rtl/*.vhd` is a hand-written single-cycle RV32I CPU with GHDL semihosting support. | Works for small baremetal tests, not generated from Simple. |
| Simple-generated RV32/RV64 FPGA Linux VHDL | `src/hardware/fpga_linux/riscv_fpga_linux.spl` generates package/top VHDL. The top increments a PC-like register, idles UART, and toggles heartbeat. | Placeholder wrapper, not CPU/SoC. |
| RV32 Linux RTL smoke | `scripts/rtl_riscv32_linux_litex.shs` uses external Linux-on-LiteX-VexRiscv. | External reference lane. |
| RV64 Linux RTL smoke | `scripts/rtl_riscv64_linux_cva6.shs` uses external CVA6. | External reference lane. |

## Direct Answer

The VHDL backend is not "none", but it is not complete enough to claim real Simple-to-RTL CPU generation. The current Simple-generated RISC-V Linux VHDL is a scaffold. Linux-capable RTL evidence currently comes from external VexRiscv/CVA6 lanes, not from Simple-generated RTL.

## Fix List

| ID | Fix | Files / area | Why |
|---|---|---|---|
| VHDL-001 | Define and enforce a synthesizable Simple hardware subset. | `src/compiler/70.backend/vhdl_constraints.spl`, docs, tests | Prevent arbitrary Simple features from reaching VHDL backend. |
| VHDL-002 | Wire and prove `simple compile --backend=vhdl` end to end. | backend factory/CLI, `examples/09_embedded/vhdl/backend/` | Current builder demos are not backend proof. |
| VHDL-003 | Add backend-generated golden examples. | `examples/09_embedded/vhdl/backend/*.spl`, `backend/golden/*.vhd` | Need visible Simple source -> generated VHDL artifacts. |
| VHDL-004 | Run GHDL analysis/elaboration for generated VHDL in tests. | system/integration tests, scripts | Text generation alone is not enough. |
| VHDL-005 | Complete MIR lowering for processes, conditionals, static loops, finite-state machines, arrays, records, and bit slices. | `vhdl_backend.spl`, `vhdl_type_mapper.spl` | Needed for non-trivial RTL. |
| VHDL-006 | Reject unsupported dynamic allocation, heap objects, recursion, dynamic loops, strings, dictionaries, runtime I/O, and pointers with diagnostics. | constraints + backend errors | Required for synthesizable output. |
| RTL-001 | Replace `RiscvFpgaLane.soc_vhdl()` PC-counter top with generated CPU/SoC modules. | `src/hardware/fpga_linux/riscv_fpga_linux.spl` or new generator modules | Current generated VHDL is not a CPU. |
| RTL-002 | Generate RV32I/RV64I core blocks first: fetch, decode, regfile, ALU, branch, load/store, CSR shell. | new `src/hardware/riscv*_rtl/*` | Establish minimal generated core. |
| RTL-003 | Add simulation parity tests against existing RV32 hand-written VHDL and emulator models. | GHDL/Verilator tests | Prevent fake "generated" progress. |
| LINUX-001 | Add privilege architecture: M/S/U modes, CSRs, traps, delegation, `mret/sret`, `sfence.vma`. | generated RTL + model tests | Linux expects S-mode under firmware/SBI. |
| LINUX-002 | Add MMU: RV32 Sv32, RV64 Sv39, TLB/page walker/faults. | generated RTL + tests | Normal Linux needs virtual memory. |
| LINUX-003 | Add CLINT/timer and PLIC/external IRQ fabric. | generated RTL + tests | Linux needs timer/external interrupt delivery. |
| LINUX-004 | Add 16550-compatible UART and memory map. | generated RTL + DTB | Needed for early console and boot markers. |
| LINUX-005 | Generate boot ROM, DTB, OpenSBI/U-Boot integration metadata. | firmware packager | Linux boot needs hart ID, DTB address, `satp=0`, alignment, and firmware services. |
| LINUX-006 | Add generated-RTL Linux smoke lane separate from external LiteX/CVA6. | scripts/check-riscv-rtl-linux-smoke.shs | Must distinguish Simple-generated proof from external reference proof. |

## Recommended Order

1. Make VHDL backend real for small combinational/sequential examples.
2. Generate and GHDL-prove a tiny RV32I subset core from Simple.
3. Run baremetal RV32 semihosting on generated RTL.
4. Grow to RV32IMA + CLINT/PLIC/UART + simple boot ROM.
5. Add RV64 path and Sv39.
6. Integrate OpenSBI/DTB and boot Linux.
