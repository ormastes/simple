# LLVM U32 Hex-Suffix Literal Lowers to Zero

## Status

open

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
