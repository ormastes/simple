# Baremetal riscv32: no real-firmware boot lane (2026-11-17)

- id: `baremetal_riscv32_no_firmware_boot_lane_2026_11_17`
- severity: P3
- status: open (blocker filed)

## What works
`native-build examples/09_embedded/freestanding_hello/main.spl --target riscv32-unknown-none --emit-object`
exits 0 (1968-byte object, phase-2 compiler, WSL Ubuntu-24.04). The freestanding
runtime `bm_rt.spl` has no division/multiply, so no compiler-rt helper is needed.

## Blocker (precise)
1. No riscv32 firmware is installed: Ubuntu 24.04 `qemu-system-data` ships only
   `opensbi-riscv64-generic-fw_dynamic.{bin,elf}`. No `opensbi-riscv32*` exists.
2. `scripts/check/check-baremetal-efi-boot.shs` has no `riscv32` arch and there is no
   `crt0_riscv32.S` (it needs `lw`/`sw` instead of the 64-bit `la`/`ld` forms, plus
   `-march=rv32imac -mabi=ilp32`).

## Next step
Build pinned OpenSBI v1.4 with `PLATFORM=generic PLATFORM_RISCV_XLEN=32 LLVM=1
FW_PAYLOAD=y`. Add `crt0_riscv32.S` and a `riscv32` case (`qemu-system-riscv32
-machine virt -bios fw_payload.bin`, payload at 0x80400000). Never `-kernel`.
