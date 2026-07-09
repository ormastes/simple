# Vulkan Engine2D Post-Test Teardown Segfault - 2026-07-09

## Severity

P1. Vulkan assertions can all pass while the interpreter process subsequently
dies during teardown, so the result is not reliable live-backend evidence.

## Component

- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
- `src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl`
- Vulkan runtime ownership behind `rt_vulkan_shutdown`

## Reproduce

```sh
SIMPLE_LIB=src bin/simple test test/02_integration/rendering/vulkan_strict_spec.spl --mode=interpreter --clean
```

On the affected Linux host, all 19 assertions print green and the runner then
prints `timeout: the monitored command dumped core` and `Segmentation fault`.
The file summary can still say `PASS`, so completion gates must inspect the
process output instead of treating that summary as proof.

## Investigation

`VulkanBackend.shutdown()` and `VulkanSession._cleanup()` previously destroyed
buffers, pipelines, and shader modules without waiting for submitted work.
Both now wait for the queue before destruction. The post-test crash remains,
which puts the remaining fault below those owner-level object lifetimes.

The session imports `vulkan_sffi_shutdown`, but calling it after every final
session release makes the focused run terminate before it can print test
results. That workaround was rejected and must not be restored without a
runtime-owned lifecycle contract that supports repeated init/shutdown cycles.

## Required Fix

Make `rt_vulkan_init` and `rt_vulkan_shutdown` safe across repeated Engine2D
probe/create/render/shutdown cycles, including device, queue, command-pool, and
loader lifetime. Add a native or interpreter subprocess regression that fails
when the child exits by signal after otherwise-green Vulkan assertions.

## Current Evidence Rule

Do not treat `vulkan_strict_spec.spl` alone as stable live Vulkan proof on this
host until the child exit is clean. The generated 2D matrix and wrapper
self-tests remain valid fail-closed contract checks, not a substitute for this
runtime fix.
