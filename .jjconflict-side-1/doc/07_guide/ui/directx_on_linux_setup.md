# DirectX on Linux — Setup Guide

This guide covers building the local DirectX prefix (`build/dx/prefix`) used
by the `directx` Engine2D backend on Linux.  No root/sudo access is required.

## What Gets Built

| Component       | Library                              | Purpose                          |
|-----------------|--------------------------------------|----------------------------------|
| vkd3d           | `build/dx/prefix/lib/libvkd3d.so`   | D3D12 → Vulkan translation        |
| dxvk-native     | `build/dx/prefix/lib/libdxvk_d3d11.so` | D3D11 → Vulkan translation    |
| system libvulkan | `/usr/lib/.../libvulkan.so.1`       | Vulkan ICD loader (probed only)  |

If both prefix builds fail the ICD leaf falls back to system `libvulkan.so.1`
(if present) or the `structured` handle path.  The `backend_directx` backend
still works in structured mode — it reports `leaf=structured` evidence rather
than `leaf=dlopen`.

## Prerequisites

```sh
# Already on this host (no install needed):
gcc, g++, cmake, ninja, git, pkg-config, spirv-as
Vulkan loader 1.3.275 + lavapipe (libvulkan_lvp.so)

# Installed automatically by the script when absent:
meson  — via: pip install --user meson
```

No `sudo` or system-package writes are performed.

## Running the Script

```sh
sh scripts/setup/setup-directx-linux.shs
```

The script is idempotent — re-running it skips already-built components.

### Environment Knobs

| Variable          | Default                    | Purpose                          |
|-------------------|----------------------------|----------------------------------|
| `DX_PREFIX`       | `<repo>/build/dx/prefix`   | Install prefix                   |
| `DX_JOBS`         | `$(nproc)`                 | Parallel build jobs              |
| `DX_SKIP_VKD3D`   | unset                      | Set to skip vkd3d build          |
| `DX_SKIP_DXVK`    | unset                      | Set to skip dxvk-native build    |

### Idempotency

The script checks for sentinel files before cloning or building:

- vkd3d: `build/dx/prefix/lib/libvkd3d.so`
- dxvk-native: `build/dx/prefix/lib/libdxvk_d3d11.so`

If either file exists the corresponding build step is skipped.

## Build Failure Handling

When a build fails the script:

1. Records a concrete blocker entry in `.spipe/gpu-backend-dx-harden/state.md`
   under `## Blockers`.
2. Continues with whatever was successfully built.
3. Writes `build/dx/prefix/dx_prefix_readiness.json` reflecting final state.
4. Reports which leaf path (`dlopen` vs `structured`) is active.

This means the `directx` backend and its specs remain runnable even when the
prefix build fails — the probe drives the expected evidence string.

## Verifying the Result

After the script completes:

```sh
# Check sentinel JSON
cat build/dx/prefix/dx_prefix_readiness.json

# Run the DirectX backend spec
bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl
```

Expected output for a host with system libvulkan but no prefix builds:

```
leaf=dlopen   (system libvulkan.so.1 found)
device_ok=true
platform=linux-dxvk
```

Expected output for a fully isolated host (no Vulkan at all):

```
leaf=structured
device_ok=true   (DXVK dispatch chain uses structured handles)
platform=linux-dxvk
```

## Leaf Evidence Contract

The Vulkan ICD SFFI shim (`src/lib/nogc_async_mut/gpu/vulkan_icd_sffi.spl`)
probes at call time:

| Condition                                     | `vk_icd_probe_leaf()` result |
|-----------------------------------------------|------------------------------|
| `build/dx/prefix/lib/libdxvk_d3d11.so` found | `leaf=dlopen`                |
| `build/dx/prefix/lib/libvkd3d.so` found       | `leaf=dlopen`                |
| `/usr/lib/.../libvulkan.so.1` found            | `leaf=dlopen`                |
| None of the above                             | `leaf=structured`            |

All `VkIcdResult` structs returned by `vk_icd_create_instance` and
`vk_icd_create_device` carry the `leaf` field.  Specs assert this field
directly — no boolean wrappers.

## Windows

On Windows the `directx` backend routes to native D3D11 (no DXVK needed) —
the same device-creation path loads the native `d3d11.dll`.  The
`dx_platform_probe()` function returns `platform=windows-native`; the leaf is
`leaf=structured` (the ICD leaf probe checks Linux prefix `.so` paths, which
do not exist on Windows).  The same spec file (`backend_directx_spec.spl`)
runs on both platforms — the probe drives which evidence strings are expected.

Validated in CI by `.github/workflows/directx-windows-validation.yml`
(windows-latest): builds the Rust seed with cargo, runs the spec in
interpreter mode (18/18, 2026-06-12), and captures probe evidence
`platform=windows-native leaf=structured device=true` — the D3D11 device is
created via the WARP software rasterizer on GPU-less runners.  The workflow
re-runs on any push touching `backend_directx.spl` or its spec, and can be
triggered manually with
`gh workflow run directx-windows-validation.yml --ref main`.
