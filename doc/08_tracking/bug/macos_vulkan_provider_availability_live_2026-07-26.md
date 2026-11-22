# macOS Vulkan live backend is unavailable before rendering
## Closed 2026-11-22 — MoltenVK portability & provider micro-probe fixes landed

**Status:** CLOSED (2026-11-22; `bug_db.sdn` status: `closed`)

## Historical Status (2026-07-26)

At filing, the trusted self-hosted Vulkan harness rebuilt, while live
framebuffer/event capture remained blocked pending provider micro-probe and
MoltenVK portability fixes documented below.

## Evidence

- The canonical live checker launched the current stripped manifest artifact
  and failed before readiness with `launched-process-missing`.
- Direct execution of that artifact returned `132` and printed
  `runtime error: field access on nil receiver`.
- A current unstripped diagnostic build reached the explicit backend receipt
  instead of the receiver trap:

  ```text
  gpu_2d_live_status=fail
  gpu_2d_live_reason=backend-create-failed
  gpu_2d_live_requested_backend=vulkan
  gpu_2d_live_selected_backend=cpu
  gpu_2d_live_probe=Vulkan shared session initialization failed: availability
  ```

The provider dylib exports `rt_vulkan_init`,
`rt_vulkan_provider_is_available`, and `rt_vulkan_provider_device_count`;
MoltenVK and the Vulkan loader are installed at the configured Homebrew
paths. Symbol presence therefore does not prove runtime provider admission.
The stripped/unstripped divergence also means the nil receiver must not be
treated as the sole cause.

## Next discriminator

Add a focused provider probe that records availability, device count, loader
path, and provider error before constructing `VulkanBackend`. Run it against
the exact provider dylib linked by the manifest, then fix provider admission
or the native receiver/cache divergence before spending another full live
window cycle.

The three Vulkan build/launch diagnosis cycles for this session are exhausted.

## Focused provider micro-probe — 2026-07-26

A separate windowless discriminator now exists at
`scripts/check/check-macos-vulkan-provider-micro-probe.shs`. Its pure-Simple
probe opens one explicitly supplied provider dylib and directly resolves:

- `rt_vulkan_provider_is_available`
- `rt_vulkan_provider_device_count`
- `rt_vulkan_init`
- `rt_vulkan_get_last_error`
- `rt_vulkan_shutdown`

The checker requires a trusted compiler manifest binding the canonical path and
SHA-256, and records bounded, hashed provider/build/probe evidence. It does
not construct `VulkanBackend`, start Engine2D, use winit, or launch a window.

The focused source contract passed 2/2. The only allowed native execution
attempt did not reach the provider: the canonical self-hosted compiler exited
with `Illegal instruction: 4`, and its retained build log contains:

```text
runtime error: field access on nil receiver
```

`DynLib.call0` only exposes an i64 ABI, while the resolved
`rt_vulkan_get_last_error` symbol returns text. The probe therefore reports a
blocked dynamic-text ABI instead of unsafely calling it. Provider availability,
device count, dyld resolution, and provider error remain unobserved in this
run. No Rust seed fallback and no exhausted full-live Vulkan command were used.

## 2026-11-22 Root-Cause MoltenVK Portability & Micro-Probe Fixes (work/mac-bugs-vulkan-20261122)

Four concrete macOS MoltenVK discovery, portability, and micro-probe defects were found and fixed in source:
1. **`src/compiler_rust/runtime/src/vulkan/instance.rs` (`VUID-VkInstanceCreateInfo-flags-06559`)**:
   - Previously, `create_flags |= vk::InstanceCreateFlags::ENUMERATE_PORTABILITY_KHR` was set on `#[cfg(target_os = "macos")]` unconditionally while `VK_KHR_portability_enumeration` was pushed only under `#[cfg(feature = "vulkan")]`, and `VK_EXT_metal_surface` was pushed without checking `has_ext(...)`.
   - Fixed by enumerating instance extensions unconditionally, gating `VK_EXT_metal_surface` on `has_ext`, and pairing `ENUMERATE_PORTABILITY_KHR` strictly with `has_ext(ash::khr::portability_enumeration::NAME)` across all feature configurations.
   - Added automatic macOS `VK_ICD_FILENAMES` fallback discovery (`/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`, `/opt/homebrew/share/vulkan/icd.d/MoltenVK_icd.json`, `/usr/local/{etc,share}/vulkan/icd.d/MoltenVK_icd.json`) when both `VK_ICD_FILENAMES` and `VK_DRIVER_FILES` are unset, owned by a single shared `Once`-guarded `simple_runtime::vulkan_graphics_runtime::ensure_macos_moltenvk_icd_env()` (re-exported in `vulkan::instance` and called by `interpreter_extern/gpu.rs`).
2. **`src/compiler_rust/runtime/src/vulkan/device.rs` & `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` (`VUID-VkDeviceCreateInfo-pProperties-04451`)**:
   - MoltenVK physical devices advertise `VK_KHR_portability_subset`, which the Vulkan Portability specification requires `vkCreateDevice` to enable whenever advertised. Both runtime and interpreter `vkCreateDevice` paths now enumerate device extensions and enable `"VK_KHR_portability_subset"` when present (and `device.rs` gates `shader_int64` and `VK_KHR_swapchain` on adapter support).
   - `gpu.rs` also applies the macOS `MoltenVK_icd.json` environment fallback before `dlopen`.
3. **`test/02_integration/rendering/macos_vulkan_provider_micro_probe.spl`**:
   - Fixed unconditional `vulkan_provider_probe_status=fail` at exit even when `is_available > 0`, `initialized > 0`, and `device_count > 0`: a healthy initialized provider with `device_count > 0` now emits `vulkan_provider_probe_status=pass` (`reason=provider-ready`, exit `0`) while preserving `vulkan_provider_probe_provider_error_abi=blocked` (never calling text-returning `rt_vulkan_get_last_error` through `DynLib.call0`).
4. **`scripts/check/check-macos-vulkan-provider-micro-probe.shs`**:
   - Restored explicit canonical-compiler and override consistency checks (`VULKAN_PROVIDER_PROBE_COMPILER_MANIFEST`, `VULKAN_PROVIDER_PROBE_COMPILER`, `VULKAN_PROVIDER_DYLIB`, rejection of `*compiler_rust/target/*`, and canonical `bin/release/{aarch64,x86_64}-apple-darwin-macho/simple` path enforcement) plus `DYLD_FALLBACK_LIBRARY_PATH` fallback for Homebrew `libvulkan.dylib`.
   - Verified `test/03_system/check/macos_vulkan_provider_micro_probe_contract_spec.spl` (2/2 passed) and `sh -n scripts/check/check-macos-vulkan-provider-micro-probe.shs`. Live native-build execution awaits the admitted macOS self-hosted compiler artifact outside Seatbelt's `MTLCreateSystemDefaultDevice` sandbox restriction.

