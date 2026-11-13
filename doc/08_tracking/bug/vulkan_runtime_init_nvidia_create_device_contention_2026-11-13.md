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
(commit "red tests"), 4 passed / 0 failed with the retry. (The helper and
these tests have since moved to the runtime crate - see § Compiled runtime lane.)

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

## Compiled runtime lane (ported 2026-11-13, follow-up to #8785)

Lanes that create a device (`git grep -lE "vkCreateDevice|create_device\("`,
owned code only):

| lane | site | state |
|---|---|---|
| seed interpreter (dlopen bridge) | `compiler/src/interpreter_extern/gpu.rs` `rt_vulkan_init_fn` | fixed by #8785 |
| compiled Rust runtime (ash) | `runtime/src/vulkan/device.rs` `VulkanDevice::new_internal` - the one `create_device` behind `rt_vulkan_init` and the `rt_vulkan_init_*_present` paths | fixed here |
| C runtime | none. `src/runtime/runtime_dynload.c` only forwards `rt_vulkan_init` to a loaded provider (`GPU_CALL0`); `runtime_native.c` has no Vulkan init | no C edit |

Out of scope: `tools/upstream-skia-ganesh-vulkan/provider.cpp` (Skia comparison
provider, its own `vkCreateDevice`, not an `rt_vulkan_init`).

Both Rust lanes now share ONE helper, the ungated
`runtime/src/vulkan_create_device_retry.rs` (`vk_create_device_with_retry`,
`vk_create_device_error`, `vk_result_name`); `gpu.rs` re-exports it and its
local copy plus tests were moved there. `rt_vulkan_init` stores the bare
`vkCreateDevice(...)` text in `last_error` (previously
`VulkanDevice::new_default: Device creation failed: ERROR_INITIALIZATION_FAILED`),
so `VulkanSession.init_error` reads `runtime-init: vkCreateDevice(device 0 of 2,
queue family 0, 5 attempt(s)): VK_ERROR_INITIALIZATION_FAILED (-3)` on both
paths. Attempts are logged with `eprintln!` (a compiled binary may have no
`tracing` subscriber). The retry sleeps while the runtime `STATE` lock is held;
that is the failure path only.

Unit tests (`cargo test --release -p simple-runtime --lib vk_create_device_retry`):
3 passed / 2 failed on the single-attempt stub (commit "red tests"), 5 passed /
0 failed with the retry.

### What "compiled path" means on this host

The deployed Linux seed links `simple-runtime` WITHOUT the `vulkan` cargo
feature (`driver/Cargo.toml` enables it for macOS only), and `native-build` is
refused (`pure-Simple tool 'native-build' unavailable; refusing Rust fallback`).
A 3-line `rt_vulkan_init()` program run by `seed-fix` returns false with
`vulkan runtime unavailable: this build of simple_runtime was compiled without
the vulkan cargo feature`. So a Simple program cannot reach a compiled device
creation here. The numbers below instead drive the runtime crate's exported
`rt_vulkan_init` / `rt_vulkan_shutdown` / `rt_vulkan_get_last_error` directly
from a Rust example binary built with `--features vulkan` (4 init / hold 300 ms
/ shutdown cycles per process; same probe source built at base and at the fix).

### Evidence (compiled runtime, probe processes failed / inits failed)

Contention source: 4 concurrent loops of the #8785 spec on `seed-fix`, running
throughout; probe run as 4 concurrent loops x 8 processes (128 inits).

| condition | base | fix |
|---|---|---|
| serial, no contender, 10 processes | 0 of 10 (0 of 40) | 0 of 10 (0 of 40) |
| 4 probe loops x 8, no contender | 0 of 32 | not run |
| 4 probe loops x 8 + spec contender, pass a | 11 of 32 (24 of 128) | 2 of 32 (2 of 128) |
| 4 probe loops x 8 + spec contender, pass b | 25 of 32 (50 of 128) | 0 of 32 (0 of 128) |

Order run: base a, [fix built], fix a, base b, fix b. Fix pass a: 16 inits hit
-3 on attempt 1; 14 recovered (6 on attempt 2, 2 on 3, 2 on 4, 4 on 5); 2
exhausted all 5 and failed closed with the full text. Fix pass b logged no
retry at all - no -3 occurred in that window - so it shows only that
contention is bursty, not that the fix removed failures. Bare probes do not
contend with each other (0 of 32, and 1 of 64 at 8 loops); the interpreter
spec processes are what provoke the driver. Base error text, all 74 failures:
`VulkanDevice::new_default: Device creation failed: ERROR_INITIALIZATION_FAILED`.

Success path: warm init (cycles 2-4 of the serial runs, n=30 each) median
157.2 ms base vs 156.6 ms fix (min 154.4 / 153.9, max 162.2 / 159.7) - one
call, no sleep, no added latency.

`backend_vulkan_rect_list_spec.spl` is unchanged by this fix: still
`expected 0 to equal 1` (0 of 1), no init failure and no retry in its log.

Interpreter lane after the helper move (seed rebuilt from this change): the
#8785 spec is 4 of 4 serially and 16 of 16 processes under 4 concurrent loops
x 4, with one init retried and recovered - same log lines as before.
