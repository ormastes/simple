# Native optional class pattern binds wrapper instead of payload

## Status

Open compiler defect. The freestanding Engine2D facade uses its explicit
backend discriminator and `Option.unwrap()` instead of payload pattern binding.

## Evidence

In the ARM64 QEMU ELF, `if val Some(backend) = self.software` passed the `Some`
heap wrapper to `SoftwareBackend.present`. The wrapper payload at offset 16 was
the real backend, while `present` interpreted wrapper offset 48 as
`dirty_tiles` and faulted at `0x4010d904`. A conditional QEMU gdb breakpoint
proved `x8=0xff000000` at that dereference and showed the wrapper/payload pair.

## Required compiler regression

Native-build a class stored in `Some(value)`, pattern-bind it, call a method,
and assert the receiver equals the payload rather than the optional wrapper.
Test both AArch64 and the host native backend. Source-side `unwrap()` is a
containment seam, not proof that general pattern lowering is fixed.
