# Engine2D Four-Backend Capture Comparison — 2026-07-24

STATUS: FAIL (all live evidence gates are fail-closed)

The shared contract requires a durable framebuffer, SHA-256 and bounds, the
ordered six-event receipt
`focus,pointer_move,pointer_down,pointer_up,key_down,key_up`, and actual backend
execution provenance. Static implementation checks are not counted as live
rendering or event evidence.

| Lane | Implementation evidence | Live render | Events | Capture/compare |
|---|---|---|---|---|
| host CPU SIMD | Native SIMD row dispatch is selected only when the runtime reports NEON/SSE/AVX/RVV; scalar-only hosts now reject `cpu_simd` | BLOCKED: no admissible pure-Simple native GUI executable | BLOCKED: native winit owners are absent | BLOCKED: no PPM/PNG |
| host Metal | Strict 4K/300-DPI harness and fail-closed wrapper exist | FAIL: pure-Simple Stage2 reached link, then missed `_rt_winit_*`; Rust-seed diagnostics are inadmissible | FAIL: no accepted receipt | FAIL: no durable capture |
| host Vulkan | Font SPIR-V validates for Vulkan 1.1; focused font/cross/wrapper specs pass | FAIL: diagnostic Rust bootstrap timed out without a window and is inadmissible | FAIL: no accepted receipt | FAIL: no durable capture |
| SimpleOS QEMU x86_64 SIMD | SSE2 fill object/disassembly and runtime receipt wiring pass static checks | FAIL: canonical native-build exited `-1` before an ELF | FAIL: no guest/QMP/PS2 receipt | FAIL: QEMU never launched |
| SimpleOS QEMU ARM64 SIMD | NEON fill object/disassembly and runtime receipt wiring pass static checks | FAIL: guest compiler is absent; direct build overflowed the linker RAM region | FAIL: PL011 cannot provide pointer or key-up/down semantics | FAIL: QEMU never launched |

No pair has two valid capture records, so pixel mismatch count, maximum channel
delta, and tolerance acceptance are intentionally not fabricated. The
comparison aggregate rejects the run.

## Required unblockers

1. Provide native owners for the winit event-loop, event, and window ABI.
2. Make strict Engine2D entry closure retain only the selected backend.
3. Produce admissible pure-Simple host executables for CPU SIMD, Metal, and
   Vulkan.
4. Produce runnable x86_64 and ARM64 SimpleOS guest ELFs.
5. Add an ARM64 input transport that can receipt pointer movement/button
   down/up and keyboard down/up.
