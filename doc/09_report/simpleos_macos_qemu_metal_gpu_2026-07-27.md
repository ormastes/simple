# SimpleOS macOS QEMU Metal GPU Audit — 2026-07-27

## Verdict

**STATUS: BLOCKED**

QEMU 10.2.2 and HVF are available on the ARM64 macOS host, and the production
ARM64 guest links after expanding its linker-owned RAM region to 368 MiB.
SimpleOS Metal GPU acceleration under QEMU is not yet verified: no supported
current-source host daemon artifact produced a fresh device-origin receipt.

## Verified observations

- Host architecture is ARM64 and HVF is supported.
- The canonical 512 MiB backing layout reserves the final 8 MiB host-GPU region
  at guest GPA `0x5f800000`.
- The former 256 MiB ARM64 link region overflowed the production desktop ELF by
  about 15.7 MiB; a 368 MiB region links while leaving headroom on the minimum
  384 MiB runner and keeping the 512 MiB host-GPU tail separate.
- Cached/diagnostic guests can boot and negotiate the protocol, but those
  artifacts do not establish current-source Metal execution.

## Blocking evidence

1. `draw_ir_adv.spl` is typed to concrete monolithic `Engine2D`.
2. The Draw IR and host-backend dependency closures share 100 files and retain
   Vulkan, OpenGL, Intel, WebGPU, and associated SFFI providers.
3. A cfg-local Metal factory did not narrow that file-level closure; the
   supported core-C attempt produced no daemon artifact.
4. Bare module-constant `match` arms lower as capture bindings. MIR builds
   normalized arms but scalar dispatch reads the original arms. A candidate
   fix could not produce a testable compiler because the available source
   driver lacks `rt_transient_array_scope_begin`.
5. Candidate-admission timeout changes did not pass the wrapper self-test
   within the three-cycle cap.

## Required completion evidence

- supported pure-Simple Metal-only daemon native build;
- exact retained QEMU HVF argv and current-source ARM64 guest;
- correlated render, Draw IR, and ProcessingIR receipts;
- positive Metal device identity and native resource handles;
- same-frame device-origin readback, never CPU-mirror promotion;
- exact packed-pixel and serialized-byte equality against the CPU/SIMD oracle;
- twenty warm samples satisfying latency and RSS limits;
- one final wrapper/self-test, environment guard, generated-spec layout, and
  independent high-capability review pass.

Linux, Windows, UNO Q, VisionFive 2, and UP Squared remain postponed or blocked
as recorded in the shared cross-host plan; none is counted as macOS evidence.
