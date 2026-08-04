# SimpleOS Browser Large-Radius Emulation Blur QEMU Timeout

## Status

Open. This blocks Clang 23.1 browser-demo acceptance criteria AC-8, AC-9, and
AC-11 in `.spipe/clang_23_1_browser_demo/state.md`.

## Current evidence

- Provider: signed `llvmorg-23.1.0-rc2`, Clang
  `b366b29d23d6f04ff880666d0a2b8d43655574c9466c9b7a1f899f2fcac0023a`.
- Bootstrap provider artifact:
  `/Users/ormastes/simple/build/native_probe/simple`, SHA-256
  `93480fcc6f062dbe6a80a8f1276fddf235520c36b4d2ef8b8ca4c8c9a4f570c1`.
- Canonical wrapper:
  `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`.
- Retained logs:
  `build/clang-23-1-qemu-evidence-sort-fix/perf-cycle1.stdout`,
  `perf-cycle2.stdout`, `perf-cycle3.stdout`, and `serial.log`.
- Cycle 1 reached Browser material admission and then stalled after a
  `0x17a420` allocation: 193,664 RuntimeValue elements (`0x2f480`), whose
  useful rectangle factors are `356x544` and `272x712`.
- Cycle 2 temporarily lowered the existing array-repeat attribution threshold
  to 128K and retained `caller=0x82acbcc`. `nm` maps that address to
  `lib__gc_async_mut__gpu__engine2d__backend_emu_adv__emu_draw_blur_rect`.
  The diagnostic threshold was restored before the next build.
- The exact rolling-sum path for radius `<= 7` passed
  `ENGINE2D_BLUR_EXACT_PROBE_PASS` under the same provider. It matches the
  original square-tap oracle for a centered radius-4 case and a clipped
  radius-2 case without intermediate rounding.
- Cycle 3 retained live QMP RIP `0x82ad0a0` in the legacy nested-tap branch,
  after its `radius <= 7` branch, proving the production command radius is
  larger. The wrapper timed out without readiness/input/framebuffer evidence.

## Required repair

1. Generalize the exact rolling-sum algorithm to the production radius without
   using an intermediate rounded horizontal blur. A safe shape is two packed
   horizontal channel-pair arrays (16 bits per channel) for radii through 127,
   with one final division after the vertical rolling sum; retain the current
   square-tap path above the proven packed-sum bound.
2. Extend the focused freestanding oracle probe to the admitted larger-radius
   bound and require byte parity plus the expected debug exit.
3. In a fresh scoped continuation, run the canonical QEMU wrapper once against
   final unchanged inputs. Require production readiness, byte-identical
   `BROWSMF.SMF`, font, framebuffer, keyboard, pointer, and browser-content
   evidence before closing AC-8.
4. Only after that pass, run the remaining compiler/core/lib/MCP, SPipe,
   direct-runtime, numbered-artifact, rendering-coupling, lint, and duplication
   gates once.

## Resume command

Use the exact `SIMPLE_BIN`, `LLVM_23_1_PREFIX`, `SIMPLE_LLVM_PREFIX`, `CLANG`,
`LINKER`, `LLVM_AR`, `SIMPLE_AR`, and `SIMPLE_LINKER` values recorded in the
SPipe state, with `BUILD_DIR=build/clang-23-1-qemu-evidence-sort-fix` and the
canonical wrapper above. Do not run a fourth QEMU attempt in the capped
2026-08-04 continuation.
