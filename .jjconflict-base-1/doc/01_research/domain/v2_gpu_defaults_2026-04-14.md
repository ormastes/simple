# V2 GPU Defaults — Per-OS engine2d Backend Recommendation

**Date:** 2026-04-14
**Scope:** V2 "Pure Simple on host OS" drawing variation (see
`doc/03_plan/gui_drawing_layer_variations.md` §2 / §5).
**Question this doc closes:** "Vulkan everywhere vs. native (Metal/DX) per OS"
— pick a per-platform default for the engine2d backend that the hosted
compositor should construct on each host.

This is research only. No source files are modified.

---

## 1. Backend status (one line each)

Status legend: **stub** = scaffolding only / FFI not wired, **partial** =
trait fully implemented but FFI runtime is half-wired or untested in CI,
**functional** = FFI surface present and used by `Engine2D.create`,
**tested** = exercised by a spec under `test/`.

| Backend | LOC | Status | Evidence |
|---|---:|---|---|
| `backend_cpu` | 444 | **functional, tested** | `src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl:1`; pure-Simple Bresenham/scanline; always reachable via `Engine2D.detect_best_backend` fallback. Exercised by `test/integration/rendering/engine2d_primitives_spec.spl`, `test/system/engine2d_primitives_spec.spl`. |
| `backend_software` | 486 | **functional, tested** | `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:1`; tile-based optimized CPU renderer with dirty-tile tracking; preferred over `cpu` when no GPU is available (`engine.spl:201`). |
| `backend_opengl` | 250 | **functional** | `src/lib/gc_async_mut/gpu/engine2d/backend_opengl.spl:23` imports the full `std.gc_async_mut.io.opengl_ffi` surface (init, FBO, draw_*, read_pixels, scissor, gradient). Availability gate `opengl_available()` at `backend_opengl.spl:90`. Headless EGL/CGL/WGL context owned by the Rust runtime. Smallest backend file because most work lives in the FFI shim. |
| `backend_vulkan` | 1263 | **functional** | `backend_vulkan.spl:32` declares `rt_vulkan_is_available()`; full GLSL compute shader pipeline per primitive (clear/rect/circle/triangle/rounded/gradient/image). Push-constant size 64B. Largest backend in the tree, and the only one with shader compilation glue (`rt_vulkan_compile_glsl`). |
| `backend_metal` | 1152 | **functional** (FFI declared, runtime untested in CI) | `backend_metal.spl:23-27` declares `rt_metal_init/is_available/device_count/create_device/destroy_device` and a full compute encoder surface. Per-kernel compute pipelines via `MTLComputeCommandEncoder`. No CI coverage on macOS hardware in this repo. |
| `backend_intel` | 924 | **partial** | `backend_intel.spl:386-390` shows a Level-Zero / SPIR-V "set_args_*" surface — the trait wrapper is present but it requires the oneAPI Level Zero runtime which the repo's Rust shim does not currently link. Treat as opt-in. |
| `backend_cuda` | 575 | **partial** | `backend_cuda.spl:1`; trait fully implemented over CUDA driver FFI; only useful on NVIDIA hosts; not on the V2 critical path. |
| `backend_rocm` | 759 | **partial** | `backend_rocm.spl:1`; HIP/ROCm parallel of the CUDA backend; AMD-only; not on the V2 critical path. |
| `backend_virtio_gpu` | 440 | **functional, OS-only** | `backend_virtio_gpu.spl:1`; relies on VirtIO MMIO/DMA — V1/baremetal only. **Excluded from V2.** |
| `backend_baremetal` | 424 | **functional, OS-only** | `backend_baremetal.spl:1`; bridges to `FramebufferDriver`. **Excluded from V2.** |

Auto-detect priority today (`engine.spl:160-201`): `cuda → rocm → metal →
vulkan → opengl → intel → software`. CPU is only reachable by explicit
`create_with_backend("cpu")`.

---

## 2. Per-OS recommendation

| OS | Default | Fallback 1 | Fallback 2 | Why |
|---|---|---|---|---|
| **macOS** | `metal` | `opengl` | `software` | Metal is the only Apple-blessed GPU API on modern macOS; MoltenVK adds an extra dependency we don't ship. The metal backend is already 1152 LOC of trait-complete code (`backend_metal.spl`). OpenGL is deprecated by Apple but still ships and is our portable cross-check. CPU/software is the always-works floor. |
| **Linux** | `vulkan` | `opengl` | `software` | Vulkan is the native-quality path on every distro that ships Mesa ≥ 19 and is the largest, most-elaborated backend in the tree (`backend_vulkan.spl`, 1263 LOC, GLSL compute kernels). OpenGL covers older GPUs and headless servers without Vulkan ICDs. Software is the floor. |
| **Windows** | `vulkan` | `opengl` | `software` | We have **no D3D11/D3D12 backend** (search `engine2d/` returns none). Vulkan ships on every Win10+ driver from NVIDIA/AMD/Intel and reuses the existing `backend_vulkan.spl` exactly. OpenGL via WGL is the legacy fallback. Recommend revisiting once a Win32 hosted surface lands (work-plan item 3). |
| **FreeBSD** | `vulkan` | `opengl` | `software` | Mesa on FreeBSD ships both Vulkan and OpenGL; no BSD-specific work needed. Same recommendation as Linux; treated as a "Linux-shaped" target until proven otherwise. |

**Rationale for not picking "Vulkan everywhere":** On macOS, MoltenVK is a
runtime translation layer we'd have to ship and version; the metal backend
already exists at the same maturity level as vulkan. The marginal cost of
keeping Metal as the macOS default is one extra `if host_os == "macos"`
branch in the selector — far less than carrying MoltenVK in the toolchain.

**Rationale for not picking native everywhere:** Windows has no D3D
backend at all in this repo, and writing one is out of scope for V2 work
plan item 3 ("Cocoa + Win32 hosted surfaces"). Reusing Vulkan for Windows
is strictly cheaper than writing `backend_dx12.spl` from scratch.

---

## 3. Gap list

Per OS, what blocks the recommended default from being viable, with the
file (or missing file) it ties to.

### macOS — default `metal`
1. **No Cocoa hosted surface.** Work-plan item 3 calls for
   `src/os/compositor/hosted_backend_cocoa.spl`; not present today
   (`ls src/os/compositor/hosted_backend_*.spl` → empty). The current
   `hosted_backend.spl` uses `rt_winit_buffer_*` FFI on a CPU pixel
   buffer (`hosted_backend.spl:120-200`) — it does **not** route through
   any `engine2d` backend at all.
2. **Metal runtime not in Rust shim CI.** `rt_metal_*` externs declared
   at `backend_metal.spl:23-27` need a corresponding Rust crate behind
   them; not exercised by any spec under `test/` (grep returns no
   `backend_metal_spec`).
3. **No `metal_available()` gate.** Other backends expose
   `opengl_available()` / `rt_vulkan_is_available()`; `backend_metal`
   declares `rt_metal_is_available` but the engine selector at
   `engine.spl:178-181` calls `MetalBackend.create().init(1,1)` blindly
   and may segfault on non-macOS hosts if the symbol is unresolved.

### Linux — default `vulkan`
1. **`rt_vulkan_compile_glsl` is the only shader compiler path.** Confirm
   the Rust runtime ships `glslang` (or `shaderc`) in the host build, or
   the 1263-line vulkan backend will fail at `init()` and silently fall
   through to `opengl` (`engine.spl:184-187`).
2. **No CI spec runs vulkan against a real Mesa ICD** — only
   `engine2d_in_qemu_spec.spl` exercises the in-QEMU path. Add a
   `test/integration/rendering/engine2d_backend_spec.spl` matrix entry
   for vulkan on the Linux runner.
3. **`hosted_backend.spl` does not yet construct an Engine2D.** Same
   structural gap as macOS — the V2 hosted path is currently CPU-only
   via `rt_winit_buffer_*` and bypasses every `backend_*` file in this
   table. Work-plan item 3 must wire one in.

### Windows — default `vulkan`
1. **No `hosted_backend_win32.spl`** (work-plan item 3, missing).
2. **WGL/Vulkan loader** — confirm the Rust runtime links
   `vulkan-1.dll` lazily and falls back rather than aborting on the many
   Windows boxes without a Vulkan ICD (older Intel iGPU drivers).
3. **No D3D backend.** Acknowledged as deferred. If we ever want
   first-class Windows feel, add `backend_d3d12.spl` — but **not for V2**.

### FreeBSD — default `vulkan`
1. **No CI runner.** Treated as best-effort. Recommend marking FreeBSD as
   "should work, untested" in `gui_drawing_layer_variations.md` until a
   runner exists.
2. Same hosted-surface gap as Linux: needs `hosted_backend.spl` to route
   through `engine2d`.

---

## 4. Backend selection mechanism

**Today:** `Engine2D.create(w, h)` calls `detect_best_backend()`
(`engine.spl:157-201`) which probes in fixed priority `cuda → rocm →
metal → vulkan → opengl → intel → software`. There is **no** environment
variable, CLI flag, or build feature that overrides this — `grep` for
`SIMPLE_ENGINE2D`, `ENGINE2D_BACKEND`, `BACKEND_OVERRIDE` across
`src/lib/gc_async_mut/gpu/engine2d/` and `src/os/compositor/` returns
nothing. The only escape hatch is the explicit
`Engine2D.create_with_backend(w, h, "name")` API at `engine.spl:81-130`,
which callers must hard-code.

**Recommended (sketch — do not implement here):**
1. Add an env var `SIMPLE_ENGINE2D_BACKEND` read once at engine init; if
   set and non-empty, pass straight to `create_with_backend` and skip
   detection. Useful for CI and bug repro.
2. Replace the fixed priority with a per-OS default table in
   `engine.spl::detect_best_backend`:
   - `macos` → `[metal, opengl, software]`
   - `linux` / `freebsd` → `[vulkan, opengl, software]`
   - `windows` → `[vulkan, opengl, software]`
3. Drop `cuda`/`rocm`/`intel` from the V2 default chain — they remain
   reachable via explicit `create_with_backend` and via
   `Engine2D.list_backends()` (`engine.spl:204-247`) for diagnostic
   surfaces, but they should not be auto-selected for drawing.

---

## 5. Non-goals

- **3D rendering.** `src/lib/gc_async_mut/gpu/renderer3d/` and any
  forward/deferred renderer are out of scope for V2 drawing.
- **ML compute paths.** `backend_cuda` and `backend_rocm` are kept in
  the codebase for `std.gpu` ML callers but are **not** V2 drawing
  defaults on any OS. Same for `backend_intel`.
- **Baremetal backends.** `backend_virtio_gpu` and `backend_baremetal`
  belong to V1 (SimpleOS / QEMU) and must not appear in any V2
  selector — the V2 hosted path should refuse to construct them.
- **Writing a D3D backend.** Acknowledged as a future option but
  explicitly not on the V2 critical path; Vulkan reuse on Windows is
  the V2 default.
