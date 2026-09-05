# Vulkan 8K retained-frame attempt — 2026-08-11

Status: BLOCKED BEFORE FRAME EXECUTION.

The intended benchmark was
`test/05_perf/graphics_2d/bench_vulkan_8k_retained_damage.spl`: 7680x4320,
one 64x64 changing rectangle, 10 warmup plus 200 timed frames. Its timed scope
includes Vulkan compute dispatch/submission/completion, exact strided
device-to-host transfer, and retained host-mirror patching. It records p50,
p95, RSS, checksum, bytes, fallback, completion, device type, and driver.

The self-hosted run did not reach Vulkan initialization. Cranelift JIT codegen
failed because the deployed runtime lacks `rt_struct_receiver_valid`, then
fell back to the interpreter. Maximum process RSS reached 12,967,500 KiB before
termination. No frame result was emitted, so no performance claim is possible.

Tracked blocker:
`doc/08_tracking/bug/vulkan_8k_benchmark_missing_struct_receiver_runtime_2026-08-11.md`.

The earlier strided-transfer-only lavapipe result remains PASS within its
narrow scope. It is not end-to-end DrawIR, swapchain presentation, or
physical-GPU evidence.

## 2026-08-12 update

The missing runtime symbol is now present, and a mirrored
`Engine2DReadback.device_identity` ABI mismatch was fixed and covered by a 2/2
focused contract. A strict-JIT run now compiles without interpreter fallback,
but reports the Vulkan shared session unavailable at its availability gate.
It still executes no frame and supplies no timing row.
