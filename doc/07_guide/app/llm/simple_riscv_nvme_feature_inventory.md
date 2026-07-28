# Simple RV32 NVMe Feature Inventory

Use this page to select a target and an honest evidence label. Detailed
operation and recovery behavior lives in
`doc/07_guide/hardware/nvme_firmware/nvme_firmware_and_emulator_guide.md`.

## Target Profiles

| ID | Configuration | Transport/media | Current boundary |
|---|---|---|---|
| `0` | `TARGET_SIMPLE_SIM` | Host NVMe model + RAM NAND | H1 software model |
| `1` | `TARGET_OPENSSD_2CH8WAY` | Cosmos+ PCIe/NFC + physical NAND | Profile present; H2 board gate postponed |
| `2` | `TARGET_OPENSSD_8CH8WAY` | Cosmos+ PCIe/NFC + physical NAND | Profile present; H2 board gate postponed |
| `3` | `TARGET_RV32_QEMU_RAM_NAND` | RV32 ELF + GDB host mailbox + guest PRP RAM + 256-byte `.nandram` | H1 firmware-command parity PASS; no AXI/IRQ |
| `4` | `TARGET_RV32_KV260_AXI_RAM_NAND` | AXI host endpoint + queue DMA + firmware mailbox + RAM NAND | H1 real firmware-in-loop PASS; board evidence open |

Unknown IDs return `TARGET_INVALID`; they never fall back to the simulator.
The canonical profile source is
`examples/09_embedded/simpleos_nvme_fw/fw/openssd_config.spl`.

## RV32/K26 Interfaces

| Interface | Address/purpose |
|---|---|
| Core DDR | `0x10000000`, instruction/data through `M_AXI_HP` |
| Firmware mailbox | `0x20000000..0x200000ff`, core-to-endpoint request/completion |
| PS control aperture | `0xA0000000`, reset/run and observation |
| PS NVMe aperture | `0xA0010000`, NVMe registers and doorbells |
| Endpoint DMA | `M_AXI_NVME_DMA`, SQE/CQE and PRP access to PS DDR |
| Interrupt | `nvme_irq` to `pl_ps_irq0` |

The RAM NAND stores 64 32-bit words in ELF section `.nandram`. It covers
erase, program, read, read-count prevention, bounded read-level retry, SECDED,
FCR, and alternate-slot recovery. It models digital firmware policy, not NAND
analog physics.

## QEMU Guest-RAM Interfaces

| Interface | Address/purpose |
|---|---|
| Firmware entry | `0x80000000` |
| GDB-driven mailbox | `0x80100000..0x80100064` |
| Write/read PRP buffers | `0x80200000` onward |
| Create CQ/SQ buffers | `0x80210000`, `0x80220000` |
| Identify buffer | `0x80240000` |
| NAND state | ELF symbol `_nandram_start`, 64 32-bit words |

These are guest RAM addresses, not MMIO/NFC/PCIe apertures. The runner derives
the NAND address from the ELF and rejects an unexpected firmware entry.

## Acceptance Commands

```sh
sh scripts/check/check-rv32-nvme-nand-recovery.shs --self-test
sh scripts/fpga/ghdl_rv32_nvme_axi_ram.shs
sh scripts/check/check-rv32-nvme-host-axi-mmio.shs
sh scripts/qemu/qemu_rv32_nvme_fw_in_loop.shs
sh scripts/fpga/ghdl_rv32_k26_ddr_boot.shs
sh scripts/check/check-nvme-firmware-remaining-gates.shs --self-test
```

Build the resident mailbox-service ELF with
`NVME_RV32_SERVICE=1 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs`;
the default build remains the internal recovery self-test image.

`rv32_nvme_host_axi_mmio` retains the focused mocked-mailbox test and passes
`rv32-nvme-fw-in-loop firmware=real transport=axi-ram`. QEMU passes
`rv32-nvme-qemu-host-parity firmware=real transport=qemu-gdb-mailbox` for the
same command/recovery sequence. QEMU `virt` has no custom endpoint, so do not
claim AXI/DMA/IRQ, PCIe enumeration, MSI/PERST, KV260 board acceptance,
physical NAND, or OpenSSD silicon from that result. The source-matched Stage 3 pure-Simple
compiler builds the resident service ELF and VHDL generator; SSpec/docgen still
requires an admitted full CLI. The stale deployed binary is not acceptable
evidence.

## Primary Files

- Endpoint RTL: `examples/09_embedded/fpga_riscv/rtl/rv32_nvme_axi.vhd`
- K26 top: `examples/09_embedded/fpga_riscv/rtl/soc_top_rv32_k26_ddr.vhd`
- RV32 firmware: `examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry.spl`
- Host SSpec: `test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl`
- QEMU runner: `scripts/qemu/qemu_rv32_nvme_fw_in_loop.shs`
- Remaining gates: `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md`
