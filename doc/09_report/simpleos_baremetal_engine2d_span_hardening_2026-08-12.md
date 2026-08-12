# SimpleOS Bare-Metal Engine2D Span Hardening — 2026-08-12

Status: **CORRECTNESS PASS / STRUCTURAL IMPROVEMENT / 8K80 UNPROVEN**

## Change

The x86-64 freestanding variable-source span now preserves the hosted
memmove-style overlap contract. When destination begins inside the same source
array, blending walks backward instead of overwriting source pixels that have
not yet been consumed. The overlap predicate avoids signed end-offset overflow.

The scalar bare-metal blend oracle now uses the exact fixed-denominator formula
for the dominant opaque-framebuffer case. Constant opaque spans use a boxed fill
loop, while transparent constants remain zero-work. Translucent destinations
retain the general straight-alpha formula.

The SimpleOS SIMD opcode checker now explicitly selects `llvm-objdump`, which
can disassemble both generated AArch64 and x86-64 objects, instead of relying on
the host GNU objdump's unsupported cross-architecture behavior.

## Evidence

- New standalone production-function oracle: PASS. It links the actual
  `baremetal_stubs.c` span functions and covers reverse overlap, invalid ranges,
  count clipping, opaque/transparent/translucent constants, tagged pixel slots,
  and unchanged return handles.
- Freestanding x86-64 source compile: PASS; both blend span symbols are present.
- Manual cross-object opcode inspection found the expected AArch64 `dup`/`st1`
  and x86-64 `pshufd`/`movdqu` instructions.
- Direct environment guard and layout checks are recorded at commit time.

The canonical cross-architecture opcode script was repaired for two concrete
tool incompatibilities, but its complete PASS line was not obtained within the
three-cycle verification cap. The standalone oracle is a hosted execution of
freestanding production functions, not a booted guest. No 8K timing, QEMU
framebuffer readback, physical scanout, or 80 fps claim is made.
