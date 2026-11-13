# Vulkan `runtime-init`: NVIDIA `vkCreateDevice` fails transiently under concurrent GPU users

- Date: 2026-11-13
- Host: DGX Spark GB10, aarch64, kernel 6.17.0-1032-nvidia, NVIDIA driver 580.173.02
  (two Vulkan devices: 0 = NVIDIA GB10, 1 = llvmpipe LLVM 20.1.2)
- Found by: PR #8765 (`engine2d_vulkan_software_showcase_frame_divergence_2026-07-02.md`,
  "3 of 10 NVIDIA spec processes" fail with a bare `runtime-init`)
- Status: error surfaced and bounded retry landed; residual documented in § Evidence (after)

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
- The first three rows also set `VK_LOADER_DEBUG=error,warn`; the loader printed
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

## Fix

1. **Error surfaced** (`gpu.rs`, `vulkan_session.spl`): every failure point of
   `rt_vulkan_init_fn` records step + `VkResult` in `VK_INIT_ERROR`, prints it
   to stderr, and `rt_vulkan_get_last_error` returns it when `VK_STATE` is
   `None`. `VulkanSession.init_error` is now `runtime-init: <step>: <VkResult>`.
   The second `vkEnumeratePhysicalDevices` result is also checked now.
2. **Bounded retry** (`vk_create_device_with_retry`, `gpu.rs`): `vkCreateDevice`
   is retried only on `VK_ERROR_INITIALIZATION_FAILED`, at most 4 more times
   after 50/100/200/400 ms (750 ms total). Every failed attempt and a late
   success are logged. Exhaustion returns the error: no CPU fallback, no skip,
   specs stay fail-closed. The success path makes one call and never sleeps.
   A persistently failing init costs up to 750 ms per call and is not cached.

Red -> green for the helper (`cargo test --release -p simple-compiler --lib
vk_create_device_retry`): 2 passed / 2 failed on the single-attempt stub
(commit "red tests"), 4 passed / 0 failed with the retry.

## Evidence (after), same spec and command

| condition | spec processes failed | retries |
|---|---|---|
| 4 concurrent loops x 8, NVIDIA (the red condition) | **2 of 32** (was 11 of 32 and 20 of 32) | 28 inits hit -3 on attempt 1; 26 recovered (8 on attempt 2, 8 on 3, 6 on 4, 4 on 5); 2 exhausted all 5 |
| 2 concurrent loops x 10, NVIDIA | 0 of 20 | 0 |
| serial, unit spec | 0 of 20 | 0 |
| serial, system spec | 0 of 10 | 1 init needed 2 retries (succeeded on attempt 3); contention source not captured. The only natural (serial) reproduction of the #8765 symptom, and it recovered |

Residual, stated rather than hidden: under four concurrent device-creating
processes 2 of 32 still fail after 750 ms, with the full error text. The bound
was deliberately not raised. Zero first-attempt failures at 2-way concurrency
and persistent ones at 4-way, with a 21 GB CUDA server process resident on the
same GPU throughout, point at a driver-side limit on concurrent clients rather
than a pure create/create race; a longer wait would only trade a clear failure
for a slow one. Running GPU specs serially (the documented rule for this host)
is unaffected.

Not changed: the compiled runtime's `rt_vulkan_init`
(`src/compiler_rust/runtime/src/vulkan_graphics_runtime_core.rs`, ash-based
`VulkanDevice::new_default`). It already records its error text via
`state.set_error`, has no retry, and was not exercised by these specs (they run
through the interpreter extern), so its behaviour under the same contention is
unmeasured.

`backend_vulkan_rect_list_spec.spl` is unchanged by this fix: still
`expected 0 to equal 1` (0 of 1), no init failure and no retry in its log.
