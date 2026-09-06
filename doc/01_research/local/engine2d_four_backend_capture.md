<!-- codex-research -->
# Engine2D Four-Backend Capture — Local Research

## Scope

Compare one deterministic Draw IR scene and one ordered input sequence across:

- macOS Metal
- host Vulkan
- host CPU SIMD
- SimpleOS QEMU CPU SIMD on x86_64 and ARM64

## Existing owners

- `src/lib/gc_async_mut/gpu/engine2d/engine.spl` selects the hosted backend.
- `backend_metal*.spl` and `metal_session.spl` own Metal execution/readback.
- `backend_vulkan*.spl` and `vulkan_session.spl` own Vulkan execution/readback.
- `backend_cpu.spl`, `backend_software.spl`, and the `simd_*` modules own hosted
  CPU SIMD rendering and execution counters.
- `src/os/compositor/engine2d_baremetal_core.spl` is the narrow SimpleOS
  framebuffer owner used because the hosted Engine2D facade is not freestanding.
- `src/app/wm_compare/graphical_backend_equality.spl` already owns tolerant
  pixel-buffer comparison.
- QEMU uses serial markers and QMP `screendump`; QMP also supports injected
  input, but guest drivers must emit a receipt before delivery is claimed.

## Gaps found

- Existing live wrappers have historically trusted self-reported backend names
  or generic pixel diversity. Neither proves the claimed renderer produced the
  captured pixels.
- The shared dirty worktree contains another agent's uncommitted Metal/Vulkan,
  vector-font, 300-DPI, and wrapper changes. Those changes are review input,
  not admissible evidence or commit provenance.
- Host CPU SIMD has real native row kernels and hit counters, while an old
  `cpu_simd` probe message still describes the path as scalar-only.
- The ARM SimpleOS framebuffer fill currently reaches a scalar runtime loop and
  the target disables NEON. It cannot honestly claim SIMD until the target and
  runtime owner are repaired and counters prove execution.
- Static screenshots do not prove focus, pointer, or keyboard delivery. Ordered
  event receipts must be tied to the same process/frame capture.

## Chosen direction

Use backend-specific adapters that emit one frozen evidence schema. Keep
transient GPU/readback details inside each backend. Compare normalized captures
through `wm_compare`, and fail closed when backend identity, SIMD counters,
event order, source revision, or capture metadata are absent.
