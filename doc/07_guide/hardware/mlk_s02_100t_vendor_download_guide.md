# MLK-S02-100T Vendor Download Guide

This guide records what is publicly verifiable for the MiLianKe `MLK-S02-100T` as of **May 2, 2026**, what is only available through the vendor portal, and what must be requested from the seller before this repo can complete board bring-up.

## Publicly Verified Facts

These facts are visible on public vendor pages or the public hardware manual.

- Public hardware manual:
  - https://www.cnblogs.com/milianke/p/17683342.html
- Public product/community page:
  - https://www.uisrc.com/forum.php?aid=24119&from=album&mobile=no&mod=viewthread&page=1&tid=6264
- Public download index:
  - https://www.uisrc.com/f-download.html
- Public AMD/Xilinx board download post:
  - https://www.uisrc.com/t-3554.html

### Confirmed Hardware Facts

From the public hardware manual:

- FPGA variants listed:
  - `XC7A35T-2FFG484I`
  - `XC7A100T-2FFG484I`
- DDR3:
  - `256MB`
  - `16-bit`
- SPI flash:
  - `W25Q128FV`
  - `128Mbit / 16MB`
- Main clock:
  - `25MHz`
- USB UART:
  - `1`
  - bridge chip `CH340K`
- User LEDs:
  - `8`
- User buttons:
  - `4`
- TF card slot:
  - present

## Important Conflict With Unverified Claims

The public manual conflicts with the spec block you supplied in a few important places.

Public manual says:
- `25MHz` onboard clock, not `50MHz`
- `256MB` DDR3 with `16-bit` bus, not `512MB` with `32-bit`

The public pages I could verify do **not** establish:
- a `125MHz` GT clock as the main board bring-up clock
- a `512MB / 32-bit` DDR3 topology for this exact board
- a public `MLK-S02-100T.xdc`
- a public Vivado project archive

Until the seller provides the real archive, those conflicting claims should be treated as unverified.

## What The Vendor Publicly Confirms About Downloads

The public AMD/Xilinx download post says the board files are distributed through the vendor download system and that customers with the matching board purchase can receive access to the board data package.

What is public:
- the download index exists
- the AMD/Xilinx board resource post exists
- access is gated behind login/VIP/purchase flow

What is **not** publicly reachable from this session:
- the actual `MLK-S02-100T.xdc`
- project `.xpr`
- HDL wrapper files
- IP `.xci`
- schematics archive
- reference design bundle

## What To Ask The Seller For

Ask for the complete archive for the exact board variant:

- `MLK-S02-100T`
- FPGA: `XC7A100T-2FFG484I`
- exact PCB revision if revisions exist

Minimum required files:

1. The authoritative `.xdc` for the `100T` board
2. Full schematic PDF
3. Pin tables or connector pinout tables if separate from the schematic
4. Vivado project or rebuild script:
   - `.xpr`
   - `.tcl`
5. Top-level HDL that matches the XDC
6. Any IP configuration files:
   - `.xci`
   - generated MIG settings
7. DDR3 reference design for the exact board
8. Simplest LED demo
9. Simplest UART demo
10. Any prebuilt `.bit`
11. Any prebuilt boot files used by their examples:
    - `fw_jump.bin`
    - `Image`
    - `.dtb`
    - rootfs or initramfs
12. Their recommended Vivado version for this exact archive
13. Any board revision notes, errata, or jumper/DIP switch notes

## What To Ask Specifically About Boot

Because this repo currently needs a concrete hardware boot path, ask for:

- the documented boot sequence for this board
- whether their flow expects:
  - JTAG-only
  - QSPI flash
  - SD card
  - UART-assisted loading
- any known-working U-Boot serial-load commands
- any expected UART baud rate if different from `115200`

If they use a soft CPU demo instead of a Linux-capable RISC-V flow, ask for that explicitly too. It still helps verify board pins and DDR wiring.

## Why XDC Alone Is Not Enough For This Repo

This repo still needs both:

- the authoritative board pin map
- a real board-level top that connects the generated core to:
  - `clk25`
  - `rst_n`
  - `uart_tx`
  - `uart_rx`
  - `led`
  - `btn`
  - DDR3 and any required memory-controller logic

So even after downloading the real XDC, bring-up is still blocked until the vendor wrapper or enough HDL/schematic data exists to wire the board correctly.

## If Work Must Continue Before The Archive Arrives

There is now an assumption-only profile in the repo:

- [mlk_s02_100t_assumed_profile.md](/home/ormastes/dev/pub/simple/doc/07_guide/hardware/mlk_s02_100t_assumed_profile.md)
- [mlk_s02_100t_assumed_unverified.xdc](/home/ormastes/dev/pub/simple/examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t_assumed_unverified.xdc)

These are intentionally non-authoritative and should only be used for provisional scaffolding work.

## Public Source Summary

Public sources used for this guide:

- CNBlogs public hardware manual:
  - https://www.cnblogs.com/milianke/p/17683342.html
- UISRC public product page:
  - https://www.uisrc.com/forum.php?aid=24119&from=album&mobile=no&mod=viewthread&page=1&tid=6264
- UISRC public downloads index:
  - https://www.uisrc.com/f-download.html
- UISRC public AMD/Xilinx board download notice:
  - https://www.uisrc.com/t-3554.html
