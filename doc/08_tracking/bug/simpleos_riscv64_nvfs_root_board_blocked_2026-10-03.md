# SimpleOS riscv64 NVFS root: physical-board run BLOCKED (2026-10-03)

**Status:** open — waiting for the physical VisionFive 2 transcript. **Lane:**
`scripts/check/check-simpleos-riscv64-nvfs-qemu.shs` (QEMU `virt`, real
firmware, PASS). **Board:** StarFive VisionFive 2 (JH7110, U74 hart 1 boots;
OpenSBI v1.2 + U-Boot 2021.10 on SPI flash per
`doc/01_research/local/starfive_visionfive2_simpleos.md`).

## Update 2026-10-04 — drivers landed, hardware run still missing

Blockers 1 and 2 below now have code; blocker 3 (no probe/serial adapter on
this host) is unchanged, so **nothing here has run on the board**.

| Piece | Code | Verified where |
|---|---|---|
| Console from FDT `/chosen stdout-path` (ns16550a byte-wide / `snps,dw-apb-uart` 32-bit, reg-shift 2) | `src/os/kernel/boot/fdt_blob.spl`, `src/os/kernel/boot/fdt_console.spl`; C sink `rv64_console_putc` in `arch/riscv64/boot/boot_entry.c` | QEMU (ns16550a path, every boot) + host spec on a JH7110-shaped DTB (`test/01_unit/os/kernel/boot/fdt_console_spec.spl`) |
| DW MSHC SD-card block driver (PIO, CMD0/8/55+41/2/3/9/7/ACMD6/16, CMD17/18/24/25/12/13) | `src/os/drivers/storage/dw_mshc_sd.spl` | Host register-model spec only (`test/01_unit/os/drivers/storage/dw_mshc_sd_model_spec.spl`); QEMU has no JH7110 model |
| NVFS on an MBR partition (SD layout p1 FAT boot, p2 NVFS) | `src/os/drivers/storage/mbr_window.spl`, entry probe in `nvfs_root_entry.spl` | QEMU: the SD-card image boots as one virtio disk; host spec over the model |
| SD-card image | `scripts/os/build-simpleos-riscv64-sdcard.shs` | Built + booted by the QEMU gate |
| Load address `0x80200000` | unchanged (correct) | JH7110 DRAM starts at `0x40000000`; 2/4/8 GiB boards all cover `0x80200000..0xA0000000` (kernel, 64 MiB heap, 8 MiB stack, DMA window `0x90000000`). U-Boot `booti` runs the Image in place (no relocation for a 2 MiB-aligned load). |

Board procedure and expected markers:
`doc/07_guide/platform/simpleos/starfive_visionfive2_simpleos.md` § "SD-card
NVFS root".

## What already transfers to the board

- Firmware path: the lane boots OpenSBI (`fw_jump`) -> U-Boot S-mode ->
  `boot.scr` -> `load ... 0x80200000 /Image` -> `booti`. The VF2 runs its own
  OpenSBI + U-Boot and executes the same `boot.scr` from the FAT partition of
  the SD card.
- The flat Image carries the RISC-V Image header
  (`check-simpleos-riscv64-image-header-contract.shs`).

## Original blockers (2026-10-03)

1. **Console:** the kernel's console was the QEMU ns16550 at `0x10000000` with
   byte access and register shift 0; VF2 UART0 is a DesignWare 8250 needing
   32-bit accesses with register shift 2. — *code landed 2026-10-04.*
2. **Root storage:** NVFS was only reachable through the QEMU virtio-mmio
   driver; no JH7110 SD (DW MSHC) block driver existed. — *code landed
   2026-10-04 (SD only; eMMC CMD1 flow and PCIe NVMe still absent).*
3. **Probe access:** no Tigard UART/JTAG probe or USB-serial adapter is
   attached to this host session, so no board identity or transcript can be
   captured. — **still open.**

## Known risks the board run must settle

- The CIU clock is not read from the clock controller: the driver assumes
  `clock-frequency` from the DTB, else 100 MHz, so identification runs at
  <= 400 kHz and data at <= 25 MHz even if the real clock is lower.
- U-Boot's control DTB (`${fdtcontroladdr}`) must name the SD controller with
  `starfive,jh7110-mmc`, `starfive,jh7110-sdio` or `snps,dw-mshc`. If the
  vendor U-Boot's DTB does not, build the card with `--board-dtb <linux dtb>`
  and `boot.scr` passes that instead.
- PIO is used on purpose (JH7110 DMA is not cache-coherent and this kernel has
  no cache maintenance); throughput is low but correctness does not depend on
  coherency.

## To close

Write `build/verify/simpleos-riscv64-nvfs/sdcard.img` to a micro-SD card, boot
it on a VF2 with a serial adapter on UART0, and record the transcript with
board identity: boot 1 must reach `NVFS_RV64_ROOT_SANITY_PASSED` with
`NVFS superblock found on dw-mshc@0x16020000 partition 2`, and boot 2 after a
cold power cycle must show `persisted:match content=nvfs-persist-ok`.
