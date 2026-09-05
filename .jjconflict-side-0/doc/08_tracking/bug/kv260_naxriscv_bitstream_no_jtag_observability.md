# KV260 NaxRiscv bitstream exposes no JTAG/PS path to softcore — physical RISC-V system test blocked

**ID:** kv260_naxriscv_bitstream_no_jtag_observability
**Severity:** P2 (blocks physical-FPGA SimpleOS/RISC-V observation, not emulation)
**Status:** Open
**Found:** 2026-06-13 (telnet-over-serial system-test bring-up)

## Finding (verified from the loaded netlist, not docs)

The currently-loaded bitstream `build/build/xilinx_kv260/gateware/xilinx_kv260.bit`
(LiteX `BaseSoC`, NaxRiscv CPU, generated 2026-05-21) exposes the softcore to
the outside world through **only two top-level ports**:

```verilog
module xilinx_kv260 (
    input  wire  serial_rx,
    output reg   serial_tx
);
```

Confirmed absences in `xilinx_kv260.v`:
- No PS→PL AXI master routed out (`ps_clk` is a clock-only black box `[BB:ps_clk]`; no `m_axi_*`/HPM ports to the PL).
- No JTAG-AXI master (matches the older `build/kria_jtag_axi/jtag_axi_inventory.txt` `hw_axis_count=0`).
- No RISC-V debug module (`[BB:NaxRiscvLitex_...]` — no `dmi`/`dtm`/`tap`/`bscan`). The `*VexRiscv*` target in `scripts/fpga/load_elf_k26.shs` belongs to a different, older design and does not exist on this bitstream.

## Consequence

On this bitstream the NaxRiscv core's **only** observable output is
`serial_tx` → PMOD pin H12 (RX on E10), LVCMOS33. There is no JTAG or
PS-memory path to read its RAM, registers, or UART. XSDB sees only the ARM DAP
(PS UART1 at 0xff01_0000 — a hard ARM peripheral, not the softcore).

Therefore the passing `check_kv260_telnet_serial_system.shs` proves only the
**bridge transport** (synthetic marker injected into PS UART1 over JTAG). A
physical SimpleOS/RISC-V console over telnet-serial is blocked on:
1. A 3.3V USB-UART adapter wired to PMOD J2 pins 1 (H12/TX) / 2 (E10/RX) / 5 (GND).
2. SimpleOS actually booting on the NaxRiscv softcore (today it boots only in QEMU).

## What IS proven (emulation)

`scripts/qemu/check_simpleos_riscv_telnet_serial.shs` (PASS 2026-06-13) boots
SimpleOS RV64 on `qemu-system-riscv64 -machine virt` via OpenSBI and observes
the real kernel marker `SimpleOS RV64` through the same telnet_serial_bridge.
This validates the OS + RISC-V + bridge chain in emulation; only the physical
silicon I/O is blocked.

## Fix options (any one unblocks physical observation; all need Vivado resynthesis ~30-60min)

- **A — route LiteX UART to a merged-USB FT4232H channel** instead of PMOD, so
  it appears on `/dev/ttyUSB*` directly (no adapter, no JTAG). Simplest.
- **B — add a PS HPM → axilite2wishbone bridge** in the LiteX platform so XSDB
  `mrd`/`mwr` (through the ARM) can read the SoC's UART CSR / `main_ram` over
  JTAG. The `axilite2wishbone_0` block already exists internally; it just needs
  its AXI-Lite slave wired to a routed PS master port.
- **C — add a NaxRiscv/VexRiscv JTAG debug module** so XSDB can halt/inspect
  the core directly (also enables `dow` ELF loading like the old VexRiscv flow).

Option A is the least-risk path to a physical SimpleOS/RISC-V telnet-serial
system test; point `QEMU_RX`/`SERIAL_PORT` at the resulting tty and reuse the
existing bridge + probe harness unchanged.
