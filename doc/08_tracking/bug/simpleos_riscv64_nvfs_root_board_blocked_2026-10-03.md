# SimpleOS riscv64 NVFS root: physical-board run BLOCKED (2026-10-03)

**Status:** open. **Lane:** `scripts/check/check-simpleos-riscv64-nvfs-qemu.shs`
(QEMU `virt`, real firmware, PASS). **Board:** StarFive VisionFive 2 (JH7110,
U74 hart 1 boots; OpenSBI v1.2 + U-Boot 2021.10 on SPI flash per
`doc/01_research/local/starfive_visionfive2_simpleos.md`).

## What already transfers to the board

- Firmware path: the lane boots OpenSBI (`fw_jump`) -> U-Boot S-mode ->
  `boot.scr` -> `load ... 0x80200000 /Image` -> `booti`. The VF2 runs its own
  OpenSBI + U-Boot and can execute the same `boot.scr` from the FAT partition of
  an SD card (`load mmc 1:1 0x80200000 /Image; booti 0x80200000 - ${fdtcontroladdr}`).
  `0x80200000` is inside VF2 DRAM (`0x40000000..`), and the flat Image carries
  the RISC-V Image header (`check-simpleos-riscv64-image-header-contract.shs`).
- The DMA window used by the virtio driver (`0x90000000`) is plain DRAM on VF2.

## Why the same artifact cannot run there today

1. **Console:** this kernel's console is the QEMU ns16550 at `0x10000000` with
   byte access and register shift 0. VF2 UART0 is a DesignWare 8250 that needs
   32-bit accesses with register shift 2 (measured 2026-08-16, research note
   above). No board/FDT-selected UART provider exists in the riscv64 boot
   runtime (`examples/09_embedded/simple_os/arch/riscv64/boot/`), so no serial
   markers would appear.
2. **Root storage:** the NVFS root is reached through
   `src/os/drivers/virtio/rv64_virtio_mmio_blk.spl` (QEMU virtio-mmio only).
   There is no JH7110 SD (DW MSHC), eMMC, or PCIe-NVMe block driver implementing
   `BlockDevice`, so NVFS cannot be mounted from board media. NVMe plans:
   `doc/03_plan/agent_tasks/starfive_visionfive2_nvme_storage.md`.
3. **Probe access:** the Tigard UART/JTAG probe used for VF2 evidence is not
   attached to this host session, so no board identity or transcript can be
   captured here.

## To close

- Add a JH7110 UART provider (DW 8250, shift 2, 32-bit) selected by board/FDT.
- Add a JH7110 block provider (SD/eMMC or PCIe NVMe) behind `BlockDevice`, and
  let `nvfs_root_entry.spl` probe it alongside virtio-mmio (still no fallback FS).
- Write the NVFS image to an SD partition, put `Image` + `boot.scr` on the FAT
  partition, capture the serial transcript with board identity, and require the
  same markers as the QEMU lane (`NVFS_RV64_ROOT_SANITY_PASSED` on boot 1 and the
  `persisted:match` marker on boot 2 after a cold power cycle).
