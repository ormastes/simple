# Baremetal riscv32: no real-firmware boot lane (2026-11-17)

- id: `baremetal_riscv32_no_firmware_boot_lane_2026_11_17`
- severity: P3
- status: verification-pending (riscv32 boots; exact transcript PASS 2026-11-17)

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

## Progress 2026-11-17 (nbm-rv32 lane) -- status: open, partially booted
- Firmware: `~/.simple/firmware/src/opensbi-1.7` builds a clang (`LLVM=1`)
  rv32 `fw_payload.bin` with `PLATFORM=generic PLATFORM_RISCV_XLEN=32
  FW_PAYLOAD=y FW_PAYLOAD_PATH=image.bin` (payload at 0x80400000, S-mode).
  `qemu-system-riscv32 -machine virt -bios fw_payload.bin` (no `-kernel`) boots it:
  banner shows `Domain0 Next Address : 0x80400000`, `Next Mode : S-mode`.
- Added `crt0_riscv32.S`. The backend lowers i64 to register pairs under ilp32
  (lo=a0/a2, hi=a1/a3), so `bm_load8`/`bm_arena_*` return `a0:a1` and `bm_store8`
  takes the value in `a2`. `bm_rt.spl` compiles for riscv32 unchanged with no
  undefined symbols.
- Link with `ld.lld -T image.ld` (base 0x80400000) and the PAYLOAD RUNS: serial
  prints `hello from Simple bare metal` -- then the transcript diverges, which
  is the remaining defect:
  1. text emitted by `print` is followed by NUL padding (a text length is read
     as a wrong/garbage value on rv32 -- suspect `rt_println_str`/`rt_println`
     length or `bm_load64` of the header on the 32-bit pair ABI);
  2. `panic("boom")` printed `explicit panic() -- diverging, must not fall
     through` instead of `panic: boom` and did not halt (`after panic` printed):
     on riscv32 the backend does not route panic through `rt_panic(ptr,len)`.
  3. `ints 0 -7 MAX MIN` and `n=42` lines are corrupted (NULs between fields).
- Not yet done: `riscv32` case in `check-baremetal-efi-boot.shs` (OpenSBI 1.7
  fw_payload build + `-march=rv32imac -mabi=ilp32`), i64 MIN print proof.
- Environment blocker hit mid-lane: C: reached 100% (2.2 GB free) and the WSL
  `Ubuntu-24.04` vhdx went `WSL_E_DISK_CORRUPTED`; no further builds possible
  until the owner repairs it. Not touched by this lane (shared with other lanes).

## RESOLVED 2026-11-17
`check-baremetal-efi-boot.shs --arch riscv32` -> `PASS -- 1 arch(es) booted through real firmware`:
`hello from Simple bare metal | n=42 | ints 0 -7 9223372036854775807 -9223372036854775808 | panic: boom`
(OpenSBI 1.7 XLEN=32 fw_payload built with clang, `qemu-system-riscv32 -machine virt -bios`, no -kernel).
The NUL-padding/panic defects above were the 32-bit pair-ABI mismatch, fixed in the runtime by
`bm_rt32.spl`; see `baremetal_32bit_i64_pair_abi_mismatch_2026-11-17.md`. The WSL disk blocker
noted above was transient and cleared. Board run not yet evidenced (riscv32 board needs its own OpenSBI platform).
