# NVMe Firmware Feature Expert

## Role

Own agent-facing knowledge for the shared Simple NVMe firmware across the host
simulator, RV32/QEMU, RV32 AXI/KV260, and Cosmos+ OpenSSD. Keep target profiles,
firmware build modes, and evidence classes separate. Never promote a host,
QEMU, GHDL, or internal self-test result to physical NVMe/NAND acceptance.

## Start Here

- Compact profile and capability inventory:
  `doc/07_guide/app/llm/simple_riscv_nvme_feature_inventory.md`
- Firmware/RAM-NAND operator guide:
  `doc/07_guide/hardware/nvme_firmware/nvme_firmware_and_emulator_guide.md`
- Cosmos+ ARM/NFC/PCIe/FSBL guide:
  `doc/07_guide/hardware/cosmos_openssd_production_firmware.md`
- Completion status and postponed physical gates:
  `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md`

## Configuration Map

The canonical target profile catalog is
`examples/09_embedded/simpleos_nvme_fw/fw/openssd_config.spl`:

| ID | Constant | Evidence boundary |
|---|---|---|
| 0 | `TARGET_SIMPLE_SIM` | Host controller/FTL/FIL with RAM NAND |
| 1 | `TARGET_OPENSSD_2CH8WAY` | Cosmos+ profile; `available=false`, H2 board gate postponed |
| 2 | `TARGET_OPENSSD_8CH8WAY` | Cosmos+ profile; `available=false`, H2 board gate postponed |
| 3 | `TARGET_RV32_QEMU_RAM_NAND` | Real RV32 ELF and firmware parity; no AXI/IRQ |
| 4 | `TARGET_RV32_KV260_AXI_RAM_NAND` | Emulation-qualified: firmware-in-loop and synthesizable K26-top GHDL PASS; physical board postponed |

Unknown IDs return `TARGET_INVALID`. New targets extend this selector and add
an evidence adapter; they do not fork command, FTL, or recovery logic.

The catalog is not yet runtime dispatch for RV32 IDs `3`/`4`. The RV32 build
script selects image behavior with `NVME_RV32_*`, and each QEMU/GHDL/board
runner supplies its transport. Treat catalog presence as configuration intent,
not proof that an executable consumed that ID.

RV32 build shape is selected independently in
`examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs`: default single-hart
self-test, `NVME_RV32_SERVICE=1` endpoint service,
`NVME_RV32_QEMU_HOST=1` QEMU parity, `NVME_RV32_BUILD_OS_BOOT=1` full OS boot,
or `NVME_RV32_SMP=1` four-hart firmware. The SMP source and host checks exist,
but its RV32 ELF/QEMU gate is blocked by compiler emission throughput.

## Media and Recovery

RV32 uses a 256-byte ELF `.nandram` region as its data/state store. It verifies
startup, admin and IO queue creation, erase, program, read, read-count refresh,
bounded read-level retry, SECDED correction, FCR, retirement, alternate-slot
verification, and remap. This is digital policy evidence, not analog NAND or
physical persistence evidence. `src/lib/hardware/nand_emu/` owns the richer
per-cell threshold model used by host simulation.

Cosmos+ binds the production firmware to dual Cortex-A9, NFC, PCIe, GIC, MMU,
L1/SCU/PL310, and a pinned FSBL/Bootgen package. Host/QEMU contracts pass. The
BT-001..BT-006 campaign is postponed until identified Cosmos+ hardware and lab
fixtures exist; it is future physical qualification, not a blocker for the
completed KV260/K26 emulation scope.

## Acceptance Commands

```sh
sh scripts/check/check-rv32-nvme-nand-recovery.shs --self-test
sh scripts/fpga/ghdl_rv32_nvme_axi_ram.shs
sh scripts/check/check-rv32-nvme-host-axi-mmio.shs
sh scripts/qemu/qemu_rv32_nvme_fw_in_loop.shs
sh scripts/fpga/ghdl_rv32_k26_ddr_boot.shs
sh scripts/check/check-nvme-firmware-remaining-gates.shs --self-test
```

After a source-matched pure-Simple CLI is admitted, run the consolidated host
gate with `--post-bootstrap`. Physical Cosmos+ evidence is accepted only by
`--board-evidence DIR`; missing board/runtime/trace data is POSTPONED or FAIL,
never a simulator fallback.

Bootstrap admission status is not inferred from a build receipt. The
current-source Phase 2 artifact recorded in
`doc/08_tracking/bug/stage2_native_sspec_process_run_sigsegv_2026-07-29.md`
passes the exact 5-scenario native SSpec and standalone docgen with zero stubs.
Use that admitted artifact for this scope; never substitute the Rust seed or
the stale deployed full CLI.

The board campaign uses `cosmos-board-campaign-v1`. It retains inventory,
commands, tools, artifact hashes, the original v3 package manifest, six BT raw
logs, `result.md`, and `manifest.txt`. Each BT-001..BT-006 PASS row includes a
relative raw-log path, its SHA-256, and the independent reviewer. The gate
rejects missing/duplicate rows, changed logs, escaping paths, duplicate fields,
same operator/reviewer, and package/source/board/artifact mismatches.

## Code Map

- Shared firmware: `examples/09_embedded/simpleos_nvme_fw/fw/`
- RV32 firmware: `examples/09_embedded/simpleos_nvme_fw/fw_rv32/`
- AXI endpoint/top/testbenches: `examples/09_embedded/fpga_riscv/rtl/`
- Cosmos+ ARM platform: `src/os/kernel/arch/arm32/cosmos/`
- System specs: `test/03_system/app/nvme_firmware/`
- RTL layer expert: `doc/00_llm_process/layer_expert/hardware_rtl/skill.md`
- RISC-V SoC expert: `doc/00_llm_process/feature_expert/riscv_soc_linux/skill.md`

## Landmines

- The profile ID and `NVME_RV32_*` build mode are different axes.
- QEMU guest RAM addresses are not MMIO apertures.
- CPU-local submission and UART markers are not host-issued NVMe evidence.
- GHDL AXI evidence is not PCIe enumeration, PERST/MSI, or board evidence.
- Cosmos+ host contracts and a valid package are not physical persistence.
- A stale or Rust-seed CLI cannot produce release SPipe evidence.
- Before a retry, verify every guide-listed RV32 NAND/AXI script, linker symbol,
  RTL endpoint, and SSpec still exists; consolidation once deleted this set
  while leaving callers and documentation intact.
