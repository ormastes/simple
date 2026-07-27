# SimpleOS macOS QEMU Metal GPU Audit — 2026-07-27

## Verdict

**STATUS: BLOCKED**

QEMU 10.2.2 and HVF are available on the ARM64 macOS host, and the production
ARM64 guest links after expanding its linker-owned RAM region to 368 MiB.
SimpleOS Metal GPU acceleration under QEMU is not yet verified: no supported
current-source host daemon artifact produced a fresh device-origin receipt.

## Verified observations

- Host architecture is ARM64 and HVF is supported.
- Draw IR now executes through the shared internal `DrawIrRenderTarget`;
  existing `Engine2D` remains its normal application implementation.
- `MetalDrawIrRenderTarget` reuses the canonical Metal backend, font renderer,
  readback record, and strict device-identity checks.
- The macOS daemon now enters through `main_macos.spl`. Its measured 202-file
  dependency closure contains no monolithic `engine.spl`, Vulkan, CUDA,
  DirectX, OpenGL, WebGPU, or other non-Metal provider.
- Focused source checks and contracts passed for the shared target, selector,
  CPU fallback, reason mapping, and protocol behavior.
- The canonical wrapper now accepts exact
  `SIMPLEOS_HOST_GPU_GUEST_ISAS=aarch64`; its shell self-test, scoped dry run,
  and focused integration spec passed. Empty, reordered, aliased, and unknown
  values fail before daemon or guest work.
- The canonical 512 MiB backing layout reserves the final 8 MiB host-GPU region
  at guest GPA `0x5f800000`.
- The former 256 MiB ARM64 link region overflowed the production desktop ELF by
  about 15.7 MiB; a 368 MiB region links while leaving headroom on the minimum
  384 MiB runner and keeping the 512 MiB host-GPU tail separate.
- Cached/diagnostic guests can boot and negotiate the protocol, but those
  artifacts do not establish current-source Metal execution.

## Blocking evidence

1. The entry-closure blocker is fixed, but no supported pure-Simple compiler
   candidate is admitted. The latest fast bootstrap reached the core-C runtime,
   exposed and fixed unavailable Darwin `closefrom`, then its final bounded
   cycle stopped during provenance fingerprinting with `No space left on
   device` before Stage 2. No daemon binary was produced.
2. No current ARM64 probe or production guest ELF exists. Existing evidence
   records `arm64-wm-target-did-not-build` and `canonical-kernel-missing`.
3. Without the daemon and guest artifacts, no fresh Metal device receipt,
   QEMU HVF frame, or exact CPU/SIMD parity sample can be collected.
4. Bare module-constant `match` arms lower as capture bindings. MIR builds
   normalized arms but scalar dispatch reads the original arms. A candidate
   fix compiled objects but its core-C runtime could not link the required
   provider symbols, so the unverified patch was not merged.
5. Candidate-admission timeout changes did not pass the wrapper self-test
   within the three-cycle cap.
6. The Metal target renders through the canonical `FontRenderer` and Metal
   atlas batch, but its `draw_ir_font_evidence()` currently returns `nil`.
   Vector-font device parity therefore remains fail-closed and cannot satisfy
   the existing 300-DPI/font promotion gate.
7. A device-seeded Metal font-oracle prototype parsed but was not merged: its
   focused suite never executed in the sparse lane, and full-frame readback
   around every font batch would violate the hot-path/performance design.

## Required completion evidence

- supported pure-Simple Metal-only daemon native build;
- exact retained QEMU HVF argv and current-source ARM64 guest;
- correlated render, Draw IR, and ProcessingIR receipts;
- positive Metal device identity and native resource handles;
- same-frame device-origin readback, never CPU-mirror promotion;
- non-nil Metal vector-font execution evidence when a vector-font fixture is
  requested;
- exact packed-pixel and serialized-byte equality against the CPU/SIMD oracle;
- twenty warm samples satisfying latency and RSS limits;
- one final wrapper/self-test, environment guard, generated-spec layout, and
  independent high-capability review pass.

Linux, Windows, UNO Q, VisionFive 2, and UP Squared remain postponed or blocked
as recorded in the shared cross-host plan; none is counted as macOS evidence.
