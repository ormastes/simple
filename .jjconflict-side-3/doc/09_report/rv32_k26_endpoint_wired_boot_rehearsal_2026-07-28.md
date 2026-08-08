# RV32 K26 endpoint-wired boot rehearsal — 2026-07-28

## Result

The current `soc_top_rv32_k26_ddr.vhd` passed the full RV32 SimpleOS boot in
GHDL with both zero-initialized and garbage-filled DDR. Both runs reached the
ordered filesystem/application markers, `K26_MARKER_SEEN`, and `TEST PASSED`
at 136922105 ns with 1,014,007 AXI reads, 95,884 AXI writes, and 443 UART
bytes. The exact counters were `0x000F78F7` reads and `0x0001768C` writes.

Commands used the cached canonical fixtures explicitly:

```sh
KERNEL_ELF=/home/ormastes/dev/pub/simple/build/os/simpleos_riscv32_smf_fs.elf \
FAT32_IMG=/home/ormastes/dev/pub/simple/build/os/fat32-riscv32.img \
sh scripts/fpga/ghdl_rv32_k26_ddr_boot.shs

GARBAGE_FILL=1 \
KERNEL_ELF=/home/ormastes/dev/pub/simple/build/os/simpleos_riscv32_smf_fs.elf \
FAT32_IMG=/home/ormastes/dev/pub/simple/build/os/fat32-riscv32.img \
sh scripts/fpga/ghdl_rv32_k26_ddr_boot.shs
```

Each run analyzed and elaborated in a fresh GHDL work library. The durable
transcripts begin with their `K26_GARBAGE_FILL` mode receipt:

- normal: `build/ghdl/rv32_k26_ddr_boot/sim.log`, SHA-256
  `df34539638c86d4c7c9bc2872a34a743ed71115a34bf9859bdfad9a0bc4b4389`
- garbage fill: `build/ghdl/rv32_k26_ddr_boot_garbage/sim.log`, SHA-256
  `5b2ea53ef74c075399c1a5e9562aa43f219ce1ac1cbdd3c2f0e8e5cf5c3d7d09`

## Provenance

- kernel ELF: `5d57d5e573722c1264a4fa35dbfc807e06a0d4f3ea356ed5a2511e9741339b89`
- FAT32 image: `35d27e11c17cd6269e561b4db2587d82d5dc6929239f00276bf9c778d7fa4db5`
- RV32 core: `4c19ffe470f7e3bd81d346f283605b96c0060dfa75fe42817b60b6d8f2b00be0`
- AXI adapter: `a19fdc4d92074c9360910ee52858508193d5746e03518944b0c14d110b061953`
- NVMe endpoint: `e971c9db04b439fd557d8a8b258fbd25b38a3ac13e6f954e12a0e10a43812bd0`
- control slave: `9c7d69e4a7cbc9ddd7184b60441b1fc4fe8f0702317fd7b0113af1a41f49ae73`
- K26 top: `0c4c809429c1a21989482a166255b7f3c2ea255c98cffb896c921cd02f40fde0`
- testbench: `0674cb327e337c9c054894f677dfb11213b439d3156498cc9e5f84004c0c36c8`

## Boundary

This proves the current generated-top AXI4/DDR and AXI-Lite boot path. The
testbench ties the NVMe endpoint off, so host-issued queue DMA/IRQ remains
proved by the separate firmware-in-loop testbench, not this boot. Vivado
bitstream and physical KV260 MMIO/JTAG evidence for the combined path remain
open.
