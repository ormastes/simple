# SimpleOS QEMU Engine2D SIMD Evidence — 2026-07-24

STATUS: FAIL (runtime evidence blocked)

Source baseline: `576be2a487176a6ee299be78aa057ada087305aa`

## Manual contract

1. launch backend
2. render deterministic scene
3. deliver input events
4. capture framebuffer
5. compare evidence

## Implemented runtime provenance

- ARM64 `rt_gui_fill4` now executes an AArch64 `dup v0.4s` plus unaligned-safe
  `st1 {v0.4s}` loop, followed by a scalar tail.
- x86_64 `rt_gui_fill4` now executes an SSE2 `movd`/`pshufd` plus `movdqu`
  loop, followed by a scalar tail.
- Runtime-owned, read-only receipts expose fill hit, vector chunk, and scalar
  tail counts. Both desktop entries fail before readiness if SIMD is disabled
  or the first frame produces zero hits/chunks.
- ARM64's target configuration enables NEON and FP-ARMv8 rather than disabling
  them.

Static cross-compilation produced AArch64 and x86_64 ELF objects. Disassembly
of each `rt_gui_fill4` confirmed the instructions above. This is implementation
evidence only; it is not a substitute for guest execution evidence.

## Launch blocker

The canonical ARM scenario stopped before guest launch because its media
preparation requires:

`bin/release/aarch64-unknown-simpleos/simple`

That pure-Simple guest payload is absent. A direct pure-Simple native-build
could not replace the canonical path: the available pure compiler has no LLVM
backend, and its Cranelift attempt overflowed the ARM linker RAM region by
31,707,136 bytes with 504 unexpected unresolved symbols. Three distinct ARM
build/launch attempts were consumed, so no further retry was made.

The x86_64 guest was not launched after the ARM-first gate failed.

## Input blocker

ARM64 currently polls PL011 character input. It can receipt a changed
character action, but it cannot distinguish key-down from key-up and has no
pointer transport. The guest emits an explicit blocker for
`pointer-down,pointer-up,key-down,key-up`; these events must not be reported as
delivered. No ordered input contract passed.

## Frozen capture fields

| Field | ARM64 | x86_64 |
|---|---|---|
| backend | `simpleos-qemu-arm64` | `simpleos-qemu-x86_64` |
| target | `aarch64-unknown-none` | `x86_64-unknown-none` |
| width | unavailable | unavailable |
| height | unavailable | unavailable |
| dpi | unavailable | unavailable |
| pixel_sha256 | unavailable | unavailable |
| non_background_bounds | unavailable | unavailable |
| event_sequence | BLOCKED | not run |
| event_count | 0 | 0 |
| event_backend | `pl011-uart` | `ps2` |
| capture_path | unavailable | unavailable |
| source_revision | `576be2a487176a6ee299be78aa057ada087305aa` | `576be2a487176a6ee299be78aa057ada087305aa` |

No PPM/PNG, framebuffer hash, bounds, cross-architecture pixel comparison, or
guest SIMD counter receipt exists. Any adapter must reject this run.
