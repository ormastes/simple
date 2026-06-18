# Simple Web Browser External Host Proof Runbook

## Purpose

This runbook covers the remaining external host gates for
`SIMPLE_WEB_BROWSER_PRODUCTION_HARDENING_2026_06_16`.

Local Linux evidence is current for Simple Web auth hardening, Electron/Tauri/
Chrome renderer parity, Vulkan/CUDA/OpenCL readback, and generated/manual spec
layout. The feature remains `current`, not `done`, until the host-specific rows
below have native proof or the selected requirements are explicitly re-scoped.

## Common Rules

- Run from the repository root.
- Prefer `SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple` when the same
  checkout path exists; otherwise set `SIMPLE_BIN` to the host's repo-local
  `bin/simple`.
- A native proof must report a positive device/backend handle where the wrapper
  exposes one, must report `device_readback` or a backend-specific native
  readback source, and must match expected/actual checksums.
- Emulation, structured contracts, `surface_upload`, provenance-only rows, and
  host-unavailable rows do not close native proof gates.
- After any pass, attach or copy the generated `doc/09_report/...` report and
  `build/.../evidence.env` fields into the handoff state.

## Local Baseline Prerequisite

Before running an external host gate, start from a checkout that includes the
2026-06-17 browser-hardening baseline:

- authenticated `/api/state` and `/api/widgets` `200 OK` JSON responses with
  no-store/no-cache/nosniff headers
- normal/shared-WM `/wm.js` and `/retained_renderer.js` script responses with
  no-store/no-cache/nosniff headers
- shown `/wm/native_window` HTML response headers
- hidden unknown-route JSON `404 not_found` fallback headers
- focused live endpoint suite passing 6 scenarios

Do not use external native readback passes to close the parent feature if this
baseline is missing or has been regressed.

## Evidence Manifest

Each external host run must produce a short manifest with these fields before
the gate can be marked closed:

| Gate | Required status field | Required source/handle field | Required report |
| --- | --- | --- | --- |
| macOS Metal | `metal_generated_2d_readback_status=pass`; `metal_engine2d_framebuffer_readback_status=pass` | Native Metal device evidence present; no `metal-requires-macos`, `host-unavailable`, or `not_device_readback` rows | Report filename pattern `doc/09_report/metal_generated_2d_readback_<date>.md` and Metal framebuffer readback report |
| AMD ROCm/HIP | `rocm_generated_2d_readback_status=pass` | ROCm/HIP device submit/readback evidence present; aggregate queue no longer reports ROCm as unavailable or non-device readback | Report filename pattern `doc/09_report/rocm_generated_2d_readback_<date>.md` and host GPU queue readback report |
| Windows DirectX | `directx_native_readback_status=pass` | Positive backend/device handle and `device_readback` source | DirectX native readback report and host GPU queue readback report |
| Browser WebGPU | `webgpu_real_readback_status=pass` | `webgpu_real_readback_source=device_readback`; `webgpu_real_readback_backend_handle` positive | WebGPU real readback report and host GPU queue readback report |

The manifest must also record host OS, GPU model, driver/runtime version,
command exit status, checksum expected/actual values, and the exact report paths
copied back into this checkout.

Use `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`
as the fillable manifest for each external run.

Before any external manifest is accepted, copy it into this checkout and run:

```sh
sh scripts/check/check-simple-web-browser-external-host-evidence-manifest.shs <manifest.md>
```

The checker must print `PASS`; otherwise the host gate remains open.

## macOS Metal Native Proof

Required host:

- macOS on Apple hardware.
- Xcode command line tools.
- `xcrun`, `metal`, `metallib`.
- At least one available `MTLDevice`.

Commands:

```sh
xcrun --find metal
xcrun --find metallib
SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-metal-generated-2d-readback.shs
SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs
SIMPLE_BIN=bin/simple sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
```

Accept only if:

- `metal_generated_2d_readback_status=pass`.
- `metal_engine2d_framebuffer_readback_status=pass`.
- The renderer parity report remains `production_gui_web_renderer_parity_status=pass`.
- No Metal row uses `metal-requires-macos`, `missing-primary-tool`,
  `host-unavailable`, `not_device_readback`, or a checksum mismatch.

## AMD ROCm/HIP Native Proof

Required host:

- Linux host with supported AMD GPU.
- ROCm/HIP runtime and compiler stack.
- `rocminfo`, `hipcc`, `libamdhip64`, `libhsa-runtime64`.
- Correct `HIP_ARCH` for the GPU, for example `gfx1100`.

Commands:

```sh
rocminfo
HIP_ARCH=gfx1100 SIMPLE_BIN=bin/simple SIMPLE_LIB=src HIPCC_TOOL=hipcc sh scripts/check/check-portable-compute-toolchains.shs
HIP_ARCH=gfx1100 SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-rocm-generated-2d-readback.shs
HIP_ARCH=gfx1100 SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Accept only if:

- `rocm_generated_2d_readback_status=pass`.
- ROCm/HIP submit and synchronization are attempted.
- Readback is available and per-operation checksums match.
- The aggregate host GPU queue report no longer reports ROCm as
  `host-unavailable`, `missing-primary-tool`, or `not_device_readback`.

## Windows DirectX Native Proof

Required host:

- Native Windows host.
- DirectX-capable GPU and driver.
- Working native Simple runtime.
- Direct3D staging/readback support.

Commands:

```sh
SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-directx-native-readback.shs
SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Accept only if:

- `directx_native_readback_status=pass`.
- DirectX native wrapper gate reports `pass`.
- Backend/device handle is positive.
- Readback source is `device_readback`.
- Expected and actual checksums match.
- The aggregate host GPU queue report no longer describes DirectX as only
  `structured_readback_contract`, `not_device_readback`, or native-pending.

## Browser WebGPU Real Device Proof

Required host:

- Browser/runtime stack with real WebGPU enabled.
- GPU adapter available to the browser.
- `src/runtime/hosted` can build with the `webgpu-real` path.

Commands:

```sh
SIMPLE_WEBGPU_REAL_TIMEOUT_SECS=180 SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-webgpu-real-readback.shs
SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Accept only if:

- `webgpu_real_readback_status=pass`.
- `webgpu_real_readback_source=device_readback`.
- `webgpu_real_readback_backend_handle` is positive.
- Expected and actual checksums match.
- The aggregate host GPU queue report no longer describes WebGPU as
  `surface_upload`, `provenance-only`, or `not_device_readback`.

## Closure Criteria

When every native proof above has accepted evidence:

1. Update `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md`
   with the passing host rows and report paths.
2. Update `doc/09_report/simple_web_browser_production_hardening.md`.
3. Change the feature DB row from `current` to `done` only if all selected
   `REQ-WEB-HARD-*` and `NFR-WEB-HARD-*` rows still trace to current evidence.
4. Run `bin/simple lint doc/08_tracking/feature/feature_db.sdn`.
5. Run the final focused verification matrix once; do not repeat already-green
   checks in a loop.
