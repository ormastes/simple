# SimpleOS RISC-V FPGA Port — Bug Tracking

Purpose: Track bugs found during SimpleOS porting and real-hardware verification on RISC-V FPGA targets (Kria K26 and DE10-Nano). Bugs are filed here during phase 7-verify.

Bug ID format: `BUG-RISCV-FPGA-NNN` (three-digit sequential)

---

## Open Bugs

| Bug ID | Title | Severity | Component | Status | Description | Fix / Workaround |
|--------|-------|----------|-----------|--------|-------------|-----------------|
| — | — | — | — | — | *(no bugs filed yet — populate during verify phase)* | — |

---

## Fixed Bugs

| Bug ID | Title | Severity | Component | Fix Commit | Description |
|--------|-------|----------|-----------|------------|-------------|
| — | — | — | — | — | — |

---

## Deferred / Won't Fix

| Bug ID | Title | Severity | Reason Deferred |
|--------|-------|----------|----------------|
| — | — | — | — |

---

## Severity Definitions

| Severity | Meaning |
|----------|---------|
| **P0** | Boot fails or data corruption — must fix before ship |
| **P1** | Core feature broken (UART, scheduler, heap) — must fix |
| **P2** | Non-critical path broken or degraded — fix if time permits |
| **P3** | Cosmetic, minor annoyance — deferred acceptable |

---

## Component Tags

| Tag | Scope |
|-----|-------|
| `boot` | M-mode entry, S-mode handoff, trap vectors |
| `uart` | UART16550 MMIO, console I/O |
| `heap` | Heap init, allocator |
| `scheduler` | Idle loop, context switch |
| `memory-map` | Address constants, `RiscvBoardMemoryMap` trait |
| `rtl-k26` | VexRiscv-SMP + AXI-HP bridge, K26 SoC wiring |
| `rtl-de10nano` | LiteX SoC, DE10-Nano gateware |
| `bitstream` | Synthesis, Vivado/Quartus output |
| `elf-load` | XSDB / openocd ELF loading |
| `platform` | `fpga.spl`, `litex_fpga.spl` platform capsules |

---

## Known Constraints (not bugs)

- **Module-level `val` constants are zero in baremetal LLVM targets** — BSS clearing wipes runtime-initialized globals. Use function-local `val` with hex literals. See memory note in `MEMORY.md`.
- **UART16550 register offsets (LSR=5, etc.) are zero in baremetal** — use `rt_riscv_uart_put` C extern directly instead.
- **LiteX is Python (third-party)** — not subject to `.spl`/`.shs` rule; invoked via `scripts/fpga/build_de10nano.shs`.

---

## Workarounds Log

| Issue | Workaround | Target Fix |
|-------|-----------|------------|
| *(none yet)* | — | — |

---

## Related Docs

- `doc/07_guide/platform/simpleos/riscv_fpga_simpleos_guide.md` — Overall FPGA guide
- `doc/07_guide/platform/misc/de10nano_quartus_setup.md` — DE10-Nano Quartus setup
- `src/os/kernel/arch/riscv64/platform/board_memory_map.spl` — Memory map trait
- `src/os/kernel/arch/riscv64/platform/kria_memory_map.spl` — K26 addresses
- `src/os/kernel/arch/riscv64/platform/litex_memory_map.spl` — LiteX/DE10-Nano addresses
