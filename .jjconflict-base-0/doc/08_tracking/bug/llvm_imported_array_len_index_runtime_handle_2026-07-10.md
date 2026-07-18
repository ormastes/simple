# LLVM Imported Array Length/Index Runtime Handle Bug

## Status

partial: HIR/MIR accessor routing fixed; native verification blocked

## Evidence

In a hosted LLVM entry closure, an imported function returning `[u32]` produces
a valid runtime array handle. The initial lowering lost unannotated binding
types, so `value.len()` lowered to constant `0` and `value[index]` lowered to a
raw pointer GEP/load.

The tracked reproducer is
`test/fixtures/compiler/llvm_simd_row_native_probe.spl`; it now uses normal
`.len()` and index syntax without declaring runtime accessors.

The post-fix retained LLVM IR reached the intended calls:

```text
call i64 @rt_array_len(ptr ...)
call i64 @rt_array_get(ptr ..., i64 ...)
```

The next bounded build exposed a separate SSA reassignment defect. A proposed
local-map rebinding was rejected because it was not CFG-safe. The final allowed
build then stopped earlier in the semantic checker with `method 'replace' not
found on value of type str in nested call context`; therefore native execution
and the strict architecture matrix remain unverified in this session.

The separate `[value; count]` pure-Simple HIR gap remains open. The span probe
now initializes through the existing typed `engine2d_simd_fill_row_u32` path;
array-repeat needs full semantic/interpreter traversal support before it should
be added to HIR rather than a SIMD-specific partial implementation.

## Impact

Imported runtime arrays are usable through the canonical runtime accessors, but
hosted LLVM code cannot yet rely on array length/index syntax for those values.

## Required Fix

Resolve the intermittent nested `str.replace` semantic failure, then run the
tracked native probe and strict x86_64/AArch64/RISC-V matrix without restoring
explicit accessor calls.

## Fresh Seed Follow-up

A Rust seed rebuilt from current source clears the stale nested `str.replace`
dispatcher failure and produces an x86_64 ELF span probe. The binary contains
`rt_engine2d_simd_fill_row_u32`, `rt_engine2d_simd_fill_span_u32`, and
`rt_array_len`, but exits `1`. Disassembly shows the dynamic imported-array
length guard folded to constant false before any `rt_array_len` call. It also
passes zero as the span color, but the retained probe source was subsequently
changed, so this binary alone does not attribute that zero to a specific
literal syntax.

The next verification must preserve runtime-array length and the exact packed
color before accepting native quality or SIMD-hit evidence.
