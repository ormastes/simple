<!-- codex-research -->
# VHDL Backend + Linux RTL Feature Options

## Option A: Make Existing VHDL Backend Real For Small Hardware Blocks

Description: finish the current MIR-to-VHDL backend for a strict synthesizable subset and prove generated VHDL with GHDL.

Pros:
- Fastest path to honest Simple source -> VHDL proof.
- Builds on existing `vhdl_backend.spl`, builder, constraints, and examples.
- Avoids premature CPU/Linux complexity.

Cons:
- Does not generate a RISC-V CPU yet.
- Requires hard diagnostics for unsupported Simple features.

Effort: M/L, about 8-14 files.

## Option B: Generate RV32I Baremetal CPU RTL From Simple

Description: use the VHDL backend/hardware DSL to generate an RV32I core comparable to the hand-written `examples/09_embedded/fpga_riscv/rtl` core, then run GHDL semihosting tests.

Pros:
- Directly addresses "Simple-generated CPU RTL".
- Has existing hand-written RV32I design and tests as oracle.
- Achievable before Linux.

Cons:
- Needs more backend maturity than Option A.
- Still not Linux-capable.

Effort: L/XL, about 15-30 files.

## Option C: Generated RV64 Linux-Capable SoC

Description: generate RV64 core + SoC RTL with Sv39, CLINT, PLIC, UART, memory bus, boot ROM, DTB/OpenSBI integration, then boot Linux under Verilator.

Pros:
- Matches real Linux target.
- Best long-term architecture.

Cons:
- Very high complexity.
- Requires CPU, privilege, MMU, bus, device, firmware, and test infrastructure all at once unless sliced carefully.

Effort: XXL, 50+ files.

## Option D: Hybrid Bridge To External Cores First

Description: keep VexRiscv/CVA6 as reference RTL cores, generate only wrapper/SoC integration/DTB/firmware from Simple first.

Pros:
- Boots Linux sooner.
- Clarifies platform generation responsibilities.
- Good comparison lane for later generated CPU.

Cons:
- Does not satisfy "CPU RTL generated from Simple".
- Risk of hiding backend gaps behind external cores.

Effort: L, about 15-25 files.

## Recommended Selection

Choose Option A + Option B first. Option C should be a later milestone after generated RV32I baremetal passes GHDL. Option D is useful only as a reference lane and must be labeled external-core.
