# Vulkan `runtime-init`: NVIDIA `vkCreateDevice` fails transiently under concurrent GPU users

- Date: 2026-11-13
- Host: DGX Spark GB10, aarch64, kernel 6.17.0-1032-nvidia, NVIDIA driver 580.173.02
  (two Vulkan devices: 0 = NVIDIA GB10, 1 = llvmpipe LLVM 20.1.2)
- Found by: PR #8765 (`engine2d_vulkan_software_showcase_frame_divergence_2026-07-02.md`,
  "3 of 10 NVIDIA spec processes" fail with a bare `runtime-init`)
- Status: see § Fix

## Symptom

`VulkanSession.init()` returned 2 with `init_error = "runtime-init"`, surfacing as
`Vulkan unavailable: Vulkan shared session initialization failed: runtime-init`
(and, through `Engine2D`, as `requested backend vulkan but got cpu`). No cause
was recorded anywhere.

## Why the error was lost

`rt_vulkan_init_fn` (`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`)
returned `Ok(Value::Bool(false))` from six different failure points and dropped
every `VkResult`. `rt_vulkan_get_last_error` reads `VK_STATE.last_error`, and
`VK_STATE` is `None` after a failed init, so it returned `""`.
`vulkan_session.spl` then wrote the constant `"runtime-init"`.

## Evidence (red)

Spec: `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_showcase_frame_parity_spec.spl`
(4 examples, each creating a device). Command per run:

```
systemd-run --user --scope -q -p MemoryMax=16G timeout 900 \
  env SIMPLE_RUST_SEED_WARNING=0 $SEED test <spec>
```

| condition | seed | spec processes failed | captured error |
|---|---|---|---|
| serial, unit spec | base seed (unmodified) | 0 of 10 | - |
| serial, system spec `showcase_vulkan_software_parity_spec.spl` | base seed | 0 of 10 | - |
| 4 concurrent loops x 8, NVIDIA (default ICD order) | error-surfacing seed, first build | 20 of 32 | `vkCreateDevice: VK_ERROR_INITIALIZATION_FAILED (-3)` x35 |
| 4 concurrent loops x 8, NVIDIA | error-surfacing seed, with device index | 11 of 32 | below, x21 |
| 4 concurrent loops x 8, llvmpipe (`VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json`) | same | 0 of 32 | - |

Captured text, identical on all 21 failing inits of the fourth row:

```
[vulkan] rt_vulkan_init failed at vkCreateDevice(device 0 of 2, queue family 0): VK_ERROR_INITIALIZATION_FAILED (-3)
Vulkan unavailable: Vulkan shared session initialization failed: runtime-init: vkCreateDevice(device 0 of 2, queue family 0): VK_ERROR_INITIALIZATION_FAILED (-3)
```

Notes on the evidence:

- The red is **self-induced contention**: the serial runs did not reproduce the
  3-of-10 reported by #8765 (0 of 20). That report was taken while other lanes
  were using the GPU; four concurrent spec loops recreate the condition.
- The first two rows also set `VK_LOADER_DEBUG=error,warn`; the loader printed
  nothing relevant.
- Failures are per init, not per process: of the 32 processes in the third row,
  12 lost one of four examples, 4 lost two, 1 lost three, 3 lost all four. A
  later init in the same process usually succeeds, so the failure is transient.

## Root cause

External to this repo. Under concurrent device creation by other processes the
NVIDIA driver returns `VK_ERROR_INITIALIZATION_FAILED` from `vkCreateDevice`.
Ruled out by the table above:

- device/queue selection nondeterminism - every failure and every success chose
  device 0 of 2 (NVIDIA GB10), queue family 0;
- `vkCreateInstance`, enumeration, command-pool creation - never the failing step;
- leaked state from a previous run - serial runs are 0 of 20;
- our loader/bootstrap code - llvmpipe through the identical code path is 0 of 32.

## Unrelated

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_list_spec.spl`
is red on this host serially (`expected 0 to equal 1`, 0 of 1 passed) with no
init failure in its log. It does not share this cause.
