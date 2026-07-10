# Vulkan Engine2D Post-Test Teardown Segfault - 2026-07-09

## Status

Resolved on 2026-07-09.

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
Both now wait for the queue before destruction.

The standalone `VulkanBackend` then released only those per-renderer objects;
the process-global logical device remained alive until C library teardown. GDB
showed the NVIDIA Vulkan driver update thread faulting while `libEGL_nvidia`
was closing from an atexit handler. The standalone shutdown path now calls the
existing `vulkan_sffi_shutdown()` after its resources are released, so the
runtime destroys the device before the loader begins process teardown.

The test runner previously replaced a nonzero child exit with an otherwise
green example summary. `test_runner_single.spl` now keeps the parsed counts but
records at least one failure for every nonzero child exit, so `simple test
test/02_integration/rendering/vulkan_strict_spec.spl --mode=interpreter --clean`
cannot report a future child crash as a passing summary.

## Verification

`SIMPLE_LIB=src bin/simple run test/02_integration/rendering/vulkan_strict_spec.spl`
now exits `0` after all 19 assertions, including repeated create/render/shutdown
cycles. The runner's nonzero-child guard remains required so a future signal
cannot be reported as a passing summary.
