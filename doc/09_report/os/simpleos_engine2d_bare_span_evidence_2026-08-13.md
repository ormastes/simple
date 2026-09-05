# SimpleOS Engine2D bare-span evidence — 2026-08-13

## Scope

This receipt verifies the freestanding x86_64 SimpleOS implementations of the
Engine2D in-place alpha blend span APIs. It is deliberately narrower than a
boot, display, or 8K throughput claim.

## Commands and results

```text
sh scripts/check/check-simpleos-baremetal-engine2d-spans.shs
simpleos-baremetal-engine2d-spans: pass

sh scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs
PASS: ARM64 NEON and x86_64 SSE2 fill kernels plus receipt symbols
```

The first command links the real
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` against
the in-place span corpus. It covers overlapping source/destination spans,
constant blend, bounds rejection, and the same-handle return convention of
`rt_engine2d_simd_blend_span_u32` and
`rt_engine2d_simd_blend_const_span_u32`.

The second command cross-compiles the ARM64 and x86_64 freestanding fill
kernels and disassembles them for NEON/SSE2 instructions plus the guest receipt
symbols. Despite its historical filename, it is a static prerequisite gate and
does not launch QEMU.

## Result boundary

The required bare runtime span symbols are linkable and behaviorally covered.
There is no current SimpleOS guest boot/readback/scanout receipt from these
commands, and they contain no 8K timing. Therefore this is not bare-metal
8K/80 proof. The actual QEMU guest render lane remains blocked upstream of
boot by the separately tracked freestanding closure/image path.
