# Vulkan Engine2D Post-Test Teardown Segfault - 2026-07-09

## Severity

P1. The direct Vulkan interpreter process dies during teardown after all
assertions print green, so the result is not reliable live-backend evidence.

## Component

- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
- `src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl`
- Vulkan runtime ownership behind `rt_vulkan_shutdown`

## Reproduce

```sh
SIMPLE_LIB=src bin/simple run test/02_integration/rendering/vulkan_strict_spec.spl
```

On the affected Linux host, all 19 assertions print green and the process exits
with `139` after `Segmentation fault`.

## Investigation

`VulkanBackend.shutdown()` and `VulkanSession._cleanup()` previously destroyed
buffers, pipelines, and shader modules without waiting for submitted work.
Both now wait for the queue before destruction. The post-test crash remains,
which puts the remaining fault below those owner-level object lifetimes.

The test runner previously replaced a nonzero child exit with an otherwise
green example summary. `test_runner_single.spl` now keeps the parsed counts but
records at least one failure for every nonzero child exit, so `simple test
test/02_integration/rendering/vulkan_strict_spec.spl --mode=interpreter --clean`
correctly exits nonzero while the runtime bug remains.

## Required Fix

Make `rt_vulkan_init` and `rt_vulkan_shutdown` safe across repeated Engine2D
probe/create/render/shutdown cycles, including device, queue, command-pool, and
loader lifetime. Add a native or interpreter subprocess regression that fails
when the child exits by signal after otherwise-green Vulkan assertions.

## Current Evidence Rule

Do not treat `vulkan_strict_spec.spl` as stable live Vulkan proof on this host
until the direct child exit is clean. The generated 2D matrix and wrapper
self-tests remain valid fail-closed contract checks, not a substitute for this
runtime fix.
