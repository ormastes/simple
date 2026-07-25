# Engine2D vulkan probe segfaults the whole process (kills list_backends + any backend-matrix spec)

- **Date:** 2026-07-21
- **Status:** FIXED + VERIFIED (same day). After the struct fix + seed rebuild,
  `probe_backend("vulkan")` returns coherently, and on this host Vulkan now
  goes all the way to **Initialized with a passing 16x16 fill+readback vs the
  SoftwareBackend oracle** (Mesa ICD). The regression gate
  `test/02_integration/gpu/engine2d_backend_matrix_spec.spl` is 14/14 green.
  Two follow-on seed extern-registry gaps were exposed once the walk survived
  vulkan and were fixed in the same change: `rt_opengl_is_available` and
  `rt_oneapi_is_available` were declared in `.spl` + implemented in
  `runtime_native.c` but never registered in the interpreter
  (`interpreter_extern/mod.rs`), so `list_backends()` died with "unknown
  extern function" at the opengl/intel slots — both now registered as honest
  interpreter-unavailable stubs.
- **Severity:** High — `Engine2D.probe_backend(_, _, "vulkan")` must return a
  `BackendProbeResult`; instead it takes down the process with SIGSEGV, so
  `Engine2D.list_backends()` and `detect_best_backend()` (when nothing earlier
  in the priority order initializes) can crash any caller, including the test
  runner mid-suite.
- **Found by:** `test/02_integration/gpu/engine2d_backend_matrix_spec.spl`
  (new SSpec verifying the 2D backend matrix). The spec's first `it` passed,
  then the runner process died during `list_backends()`; isolated outside the
  runner with `bin/simple run`.

## Minimal repro (8 lines, crashes every time)

`build/.vulkan_only_probe.spl`:

```simple
use std.gpu.engine2d.engine.{Engine2D}
use std.gpu.engine2d.backend_probe.{backend_status_text}

print("before-vulkan-probe")
val p = Engine2D.probe_backend(4, 4, "vulkan")
val st = backend_status_text(p.status)
print("vulkan: {st}")
print("after-vulkan-probe")
```

```
$ timeout 120 bin/simple run build/.vulkan_only_probe.spl
before-vulkan-probe
Segmentation fault    (exit 139)
```

`"vulkan: ..."` never prints — the crash is inside
`Engine2D.probe_backend` → `VulkanBackend.create()/init()`
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl:626-633` →
`backend_accel_vulkan.spl` → `std.nogc_sync_mut.gpu.engine2d.sffi_vulkan` /
`std.nogc_sync_mut.io.vulkan_sffi`), i.e. in the native vkCreateInstance /
loader path, not in spec code.

## Wider probe evidence (same binary, same host, sequential probes)

```
cpu:      Initialized
software: Initialized
metal:    Unavailable            <- coherent, expected on Linux
vulkan:   SIGSEGV (exit 139)     <- crash instead of a probe result
--- run with vulkan skipped ---
cpu_simd: Initialized
directx:  Initialized (DirectX(software-emulation raster) initialized)
cuda:     Initialized
```

`detect_best_backend()` returns `"cuda"` on this host, so the vulkan probe is
skipped there (cuda wins at priority position 2) — but `list_backends()`
always walks the FULL priority order and therefore always hits the crash:
`metal -> cuda -> rocm -> qualcomm -> vulkan(SEGV)`.

## Host / binary identity

- Host: Linux x86_64, headless; GPUs: NVIDIA RTX A6000 + NVIDIA TITAN RTX
  (`nvidia-smi -L`).
- Vulkan loader present with many Mesa ICDs (`libvulkan_nouveau.so`,
  `libvulkan_radeon.so`, `libvulkan_virtio.so`, `lvp`, `intel`, ...) but NO
  NVIDIA proprietary Vulkan ICD listed in `/usr/share/vulkan/icd.d/`.
- Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, which
  self-reports: "WARNING: this Rust-built Simple binary is a bootstrap seed
  only". So this evidence is attributed to the SEED build; re-verify on the
  pure-Simple self-hosted binary once redeployed (testing.md binary-identity
  caveat).

## Impact

- `test/02_integration/gpu/engine2d_backend_matrix_spec.spl` FAILS on this
  host (runner dies mid-suite: Files: 1, Passed: 0, Failed: 1). The spec is
  correct and stays as-is — a probe API that can segfault is the defect.
- Any production caller of `list_backends()` on a machine with this Vulkan
  loader/ICD combination crashes.

## Expected behavior

`probe_backend(w, h, "vulkan")` must NEVER crash: any loader/ICD failure must
be caught and surfaced as `BackendStatus.Unavailable`/`Failed` with
`available == false` and a non-empty reason (same contract every other
backend honors, see `metal: Unavailable` above).

## Root cause (2026-07-21, gdb backtrace + struct-layout audit)

gdb places the fault in the seed's extern shim, NOT in the loader/ICD:

```
Thread 2 "simple-main" received signal SIGSEGV
#0 simple_compiler::interpreter::interpreter_extern::gpu::rt_vulkan_device_type_fn
#1 core::ops::function::FnOnce::call_once
#2 ...::call_extern_function_with_values
```

`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` declares a
hand-rolled `#[repr(C)] VkPhysicalDeviceProperties` with
`_limits_and_sparse: [u8; 524]` → total struct size **816 bytes, align 4**.
The real C struct is **824 bytes, align 8** (header 292 + 4 pad so
`VkPhysicalDeviceLimits` starts 8-aligned at 296 + limits 504 + sparse 20 +
4 tail pad). `vkGetPhysicalDeviceProperties` therefore writes 4–8 bytes past
the stack allocation on every call — with the NVIDIA driver this smashes the
frame and SIGSEGVs. All three shims that build this struct on the stack were
affected (`rt_vulkan_device_type_fn` via `vulkan_device_properties`,
`rt_vulkan_device_name_fn`, `rt_vulkan_selected_device_*`).

**Fix:** `_limits_and_sparse: [u8; 524]` → `[u8; 532]` and
`#[repr(C)]` → `#[repr(C, align(8))]` (3 sites in gpu.rs), making the Rust
struct exactly sizeof 824 / align 8. Requires a seed rebuild to take effect;
`test/02_integration/gpu/engine2d_backend_matrix_spec.spl` is the regression
gate (its vulkan matrix entry + `list_backends` its crash without the fix).

## Notes

- Repro scripts kept at `build/.vulkan_only_probe.spl`,
  `build/.backend_probe_script.spl`, `build/.rest_probe.spl` (gitignored).
- Working copy at repro time also carried 33 unresolved jj-conflict files in
  `src/` (separate parallel-session issue); the two conflicts in
  `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` were resolved to
  side #1 (scalar-mirrors fix) to even let the spec load — the vulkan SEGV
  reproduces independently of that.
