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
| `4` | `TARGET_RV32_KV260_AXI_RAM_NAND` | AXI host endpoint + queue DMA + firmware mailbox + RAM NAND | H1 firmware-in-loop and current-top GHDL boot PASS; board evidence open |

Unknown IDs return `TARGET_INVALID`; they never fall back to the simulator.
The canonical profile catalog is
`examples/09_embedded/simpleos_nvme_fw/fw/openssd_config.spl`.

Target IDs describe hardware/media contracts. The current RV32 build does not
consume IDs `3`/`4`; `NVME_RV32_*` selectors below choose the executable image,
and its runner supplies the transport. Do not claim runtime profile dispatch
from the catalog alone.

## Firmware Build Modes

| Mode | Selector | Artifact / boundary |
|---|---|---|
| Single-hart self-test | default | `build/nvme_fw_rv32.elf`; internal startup, queues, NAND prevention/recovery |
| Resident endpoint service | `NVME_RV32_SERVICE=1` | `build/nvme_fw_rv32_service.elf`; serves the AXI firmware mailbox |
| QEMU host parity | `NVME_RV32_QEMU_HOST=1` | `build/nvme_fw_rv32_qemu_host.elf`; implies service mode and uses guest-RAM mailbox/PRPs |
| Full RV32 OS boot | `NVME_RV32_BUILD_OS_BOOT=1` | Slower diagnostic build through the SimpleOS boot graph |
| Four-hart firmware | `NVME_RV32_SMP=1` | `build/nvme_fw_rv32_smp.elf`; host logic checks exist, RV32 ELF/QEMU admission remains blocked by compiler emission throughput |

`NVME_RV32_SIMPLE_BIN`, `NVME_RV32_OUT`, and
`NVME_RV32_BUILD_TIMEOUT_SECS` override the compiler, output, and timeout.
`build.shs --background` starts a detached build and `build.shs --status`
reports its artifact and last phase. A background receipt is not a PASS until
the expected ELF and its target runner pass.

## Platform Capability Boundary

| Capability | RV32 QEMU | RV32 GHDL/KV260 | Cosmos+ ARMv7 |
|---|---|---|---|
| CPU | QEMU RV32IMAC, one hart | Simple RV32 soft core, current admitted path is one hart | Zynq-7000 dual Cortex-A9 |
| Queue transport | Guest-RAM mailbox and PRPs | AXI MMIO, SQE/CQE/PRP DMA, IRQ in GHDL | PCIe command FIFO/SRAM and host DMA contract |
| Media | 256-byte linker RAM NAND | Same `.nandram` over AXI or BRAM | 8-channel/8-way physical NAND through NFC |
| SMP/GIC | Not claimed | Four-hart source/host checks only; no admitted RV32 SMP ELF | CPU1/GIC/cache host contracts pass; physical SMP gate open |
| MMU/cache | Not used by direct firmware | Direct M-mode firmware; no MMU claim | MMU W^X, L1, SCU and PL310 host/QEMU contracts pass |
| FSBL/boot | `-bios none`; not FSBL evidence | KV260 PS init/JTAG flow; tiny BRAM needs no FSBL | Pinned FSBL/Bootgen package exists; physical handoff gate open |
| Physical acceptance | None | No retained source-matched current bundle; host-issued physical NVMe sequence open | NFC/PCIe/persistence BT-001..BT-006 open |

The Cosmos+ ARM, NFC, PCIe, SMP/GIC, cache/MMU, and FSBL implementation and
acceptance commands are documented in
`doc/07_guide/hardware/cosmos_openssd_production_firmware.md`. Do not infer
those capabilities from the RV32 soft-core profile.

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

Current bootstrap admission is tracked in
`doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md`. Retry 14
used pushed authority `3962be916c9d`, rebuilt the Rust authority, compiled all
Stage 2 objects, and stopped at the native link after 24m01s on three stale
symbol groups: an undeclared trait-lowering helper, removed coverage-inventory
calls, and CUDA sizing lowered to unavailable bare `sum`. Peak RSS was
2,591,760 KiB with zero swap. The source repairs now materialize imported
traits through `lower_trait`, remove orphaned coverage calls, and use explicit
CUDA size accumulation. Retry 15 is the next bounded admission attempt; no
replacement full CLI is admitted yet. Do not run release SSpec/docgen or claim
source-matched firmware GHDL evidence with the Rust seed or a stale deployed
binary.

The current endpoint-wired K26 top also passes full SimpleOS boot with both
zeroed and garbage-filled DDR. That rehearsal uses a tied-off endpoint and does
not replace the firmware-in-loop DMA/IRQ gate or physical board evidence.

## Primary Files

- Endpoint RTL: `examples/09_embedded/fpga_riscv/rtl/rv32_nvme_axi.vhd`
- K26 top: `examples/09_embedded/fpga_riscv/rtl/soc_top_rv32_k26_ddr.vhd`
- RV32 firmware: `examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry.spl`
- Host SSpec: `test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl`
- QEMU runner: `scripts/qemu/qemu_rv32_nvme_fw_in_loop.shs`
- Remaining gates: `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md`
- LLM feature expert: `doc/00_llm_process/feature_expert/nvme_firmware/skill.md`
