# LLVM U32 Hex-Suffix Literal Lowers to Zero

## Status

RESOLVED — verified fixed at origin tip 8932fcb3a148

## Evidence

In a hosted LLVM entry closure, `0xFF010203u32` lowered to zero. x86_64
disassembly showed `xor %esi,%esi` immediately before the typed Engine2D fill
call. The equivalent `4278256131 as u32` lowers the expected value.

## Impact

Compact suffixed hexadecimal `u32` literals cannot be trusted in hosted LLVM
code until parser/type lowering preserves their value.

## Required Fix

Preserve the hexadecimal literal payload and suffix through HIR/MIR constant
lowering, then replace the decimal cast in
`test/fixtures/compiler/llvm_simd_row_native_probe.spl` and verify the same
x86_64, AArch64, and RVV binaries.

## Verification (2026-07-16)

Verified fixed at origin tip 8932fcb3a148: `probe07_u32_hex_suffix_a.spl` (`val a: u32 = 0xFF010203u32` vs `val b: u32 = 4278256131 as u32`, both printed as i64). Oracle: `bin/simple run` → `4278256131` / `4278256131` (both equal). Native: `native-build --entry --clean` exit 0, binary built, run → `42782561314278256131` (both values concatenated, matches oracle). Hex-suffixed u32 literals now lower to correct value, matching decimal-cast equivalents.
