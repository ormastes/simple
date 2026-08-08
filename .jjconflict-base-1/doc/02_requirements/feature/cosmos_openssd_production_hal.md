# Cosmos+ OpenSSD Production HAL Requirements

## Scope and Baseline

These requirements cover the Zynq-7000/Cortex-A9 platform HAL, boot image, and
production evidence for the CRZ Cosmos+ OpenSSD 8-channel/8-way board. The PL
register baseline is upstream Cosmos+ OpenSSD commit
`78601486bb5581e40628ec7e841dea8e97eff034`, especially
`GreedyFTL-3.0.0`, `tiger4_nfc_substrate-1.0.0`,
`nvme_host_ctrl_8lane-1.0.0`, and
`OpenSSD2-8C8W-Prebuild-3.0.0.hdf`.

Passing host or QEMU tests proves only the hardware-independent software
contract. A production claim additionally requires the board evidence in
REQ-011 and REQ-012.

## Functional Requirements

- **REQ-001 - Fail-closed profile binding.** QEMU shall never access PL
  apertures. A silicon image shall access NFC or PCIe only when its build is
  bound to the verified 8Ch8Way v3.0.0 bitstream contract. An unbound or
  mismatched profile shall return `COSMOS_UNAVAILABLE` or fail compilation,
  never probe an assumed address.
- **REQ-002 - NFC register and geometry contract.** The NFC HAL shall bind eight
  Tiger4NSC channels at `0x43C00000 + channel * 0x10000`, eight ways per
  channel, 16 KiB data plus 256-byte spare pages, 256 rows per erase block, and
  the two upstream LUN row ranges. Register offsets and uProgROM command values
  shall match the pinned upstream HDF/RTL/software contract.
- **REQ-003 - NFC operations and recovery.** The NFC HAL shall provide bounded,
  per-channel serialized reset/toggle-mode initialization, status, page read,
  page program, and block erase. It shall validate channel, way, row, erase
  alignment, DMA range, DMA overlap, completion, NAND status, and ECC metadata.
  A timeout shall quarantine that channel until platform reset; controller-owned
  DMA buffers shall not be reused after timeout.
- **REQ-004 - PCIe/NVMe endpoint readiness.** The PCIe HAL shall bind the
  upstream NVMeHostController aperture at `0x83C00000` only for contract token
  `COSMOS_PCIE_CONTRACT_8CH8WAY_V300`. It shall use bounded, stable snapshots to
  validate link-up/LTSSM, Bus Master, MSI, MSI-X exclusion, MME range, NVMe
  enable/ready state, and paired admin SQ/CQ validity.
- **REQ-005 - ARMv7 freestanding runtime.** The image shall provide the memory,
  string, ARM EABI memory, 32-bit signed/unsigned division, divide-by-zero hook,
  and unwind-failure primitives required before Simple runtime handoff. It shall
  use no host libc, heap, or dynamic loader.
- **REQ-006 - SMP and GIC.** CPU0 shall initialize GICv1 distributor and CPU
  interface state. CPU1 release shall follow the Zynq protocol: write an
  ARM-aligned secondary entry to `0xFFFFFFF0`, execute `DSB`, issue `SEV`, and
  use a generation-tagged bounded mailbox. CPU1 shall acknowledge only after
  its MMU/cache/coherency and GIC CPU interface initialization succeeds.
- **REQ-007 - MMU and cache.** Each core shall install the same 16 KiB short
  descriptor table, enable SCU and `ACTLR.SMP` before caches, use correct
  set/way operands and TTBR0 WBWA attributes, and enable MMU/L1 caches. CPU0
  shall initialize PL310 with bounded maintenance. DDR shall be normal cached;
  NFC, PCIe, UART, SLCR, GIC, SCU, and PL310 shall be device memory; high OCM
  shall be normal uncached/XN.
- **REQ-008 - FSBL handoff and exception containment.** Silicon startup shall
  install VBAR and abort handlers before optional PL access. It shall
  read-only validate locked SLCR state, active ARM/DDR clocks at offsets
  `0x120`/`0x124`, released PS/CPU0 resets, and `DEVCFG.INT_STS.PCFG_DONE`.
  Foundational runtime, MMU, or GIC failure shall prevent FSBL, PL, and CPU1
  progression.
- **REQ-009 - Integrated boot verdict.** UART polling shall be bounded. QEMU
  success shall require runtime, MMU/cache, and primary GIC success while CPU1,
  FSBL, NFC, and PCIe remain explicitly unavailable. Silicon success shall
  require every mandatory lane to return `COSMOS_OK`. No unavailable, timeout,
  abort, unknown status, or missing marker may produce a silicon PASS.
- **REQ-010 - Reproducible boot packaging.** Packaging shall require explicit
  FSBL ELF, bitstream, silicon firmware ELF, and output paths; reject aliases,
  malformed/empty/non-ARM/non-`ET_EXEC`/zero-entry/no-`PT_LOAD` inputs; verify
  Xilinx bitstream synchronization and Bootgen partition metadata; and publish
  a manifest containing canonical paths, profile/board identity, and SHA-256
  hashes for every input and output.
- **REQ-011 - Hardware-independent evidence.** Release preparation shall include
  strict QEMU and silicon-profile builds, exact QEMU markers, runtime edge
  checks, packaging rejection tests, and executable host mock-MMIO tests for
  FSBL, NFC, PCIe, SMP mailbox/GIC, cache operands/PL310, bounded timeouts, and
  abort/fail-closed behavior.
- **REQ-012 - Board acceptance.** Production release shall retain identified
  board, toolchain, FSBL, bitstream, firmware, and `boot.bin` hashes plus serial
  and host logs proving BootROM/FSBL boot, all 64 NAND targets and ECC behavior,
  NAND power-loss recovery, PCIe BAR/MSI/reset/DMA/queue behavior, and dual-core
  interrupt/cache coherency stress. Board acceptance shall not be inferred from
  QEMU, compilation, source guards, self-tests, or synthetic Bootgen fixtures.
- **REQ-013 - Multi-target firmware configuration.** The target-neutral NVMe
  command, FTL, and recovery core shall select an explicit configuration for
  Simple simulation, QEMU/FEMU, Cosmos+ OpenSSD 2Ch8Way and 8Ch8Way, and
  KV260/FPGA. Each profile shall declare geometry, transport, media, MMIO,
  runner, capability state, and evidence class. Unknown or unavailable
  hardware targets shall fail closed and shall never execute as the simulator.

## Current Claim

As of 2026-07-26, scoped H1 runners passed for runtime ABI, MMIO, PCIe
IRQ-61/command-completion/host-DMA transport, NVMe IO callback core, corrected
PCIe bridge and NVMe admin cores, SMP/cache, QEMU boot, silicon build, and
package self-test. Corrected bridge/admin evidence covers Abort bits,
Number-of-Queues NSID/max, CQ IEN/IV, SQ QPRIO, SMART NSID/RAE, zero-write-only
completion retry, non-retryable post-start completion, and PRP edges. The
silicon composition now binds persistent FTL/NFC media, 4 KiB-to-16 KiB
staging, fail-closed UART foreground dispatch, page-tag validation, and
transactional ECC refresh relocation. No current `bin/release/simple` exists.
Official Bootgen v2026.1, the pinned bitstream, vendor FSBL, and a real package
are retained locally. Package manifest v3 now binds clean repository, complete
compiled-source closure, tools, profile/contract, board identity, boot mode,
DMA bounds, and artifact hashes with omission/mutation rejection. Current
SSpec/docgen evidence and all physical board evidence remain absent.
The supported claim is **production BLOCKED/FAIL; silicon acceptance is not
established**.
