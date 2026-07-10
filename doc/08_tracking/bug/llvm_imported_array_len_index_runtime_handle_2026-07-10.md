# LLVM Imported Array Length/Index Runtime Handle Bug

## Status

open

## Evidence

In a hosted LLVM entry closure, an imported function returning `[u32]` produces
a valid runtime array handle. Direct `rt_array_len` and `rt_array_get` calls
return the expected length and pixels, but `value.len()` lowers to constant `0`
and `value[index]` lowers to a raw pointer GEP/load.

The tracked reproducer is
`test/fixtures/compiler/llvm_simd_row_native_probe.spl`; its runtime accessor
calls are intentional until the sugar routes through the same ABI.

## Impact

Imported runtime arrays are usable through the canonical runtime accessors, but
hosted LLVM code cannot yet rely on array length/index syntax for those values.

## Required Fix

Preserve the imported array return type through the let-bound receiver and
route `.len()` plus indexing through `rt_array_len` / `rt_array_get`. Verify the
same tracked probe after replacing the explicit accessor calls with array
syntax.
