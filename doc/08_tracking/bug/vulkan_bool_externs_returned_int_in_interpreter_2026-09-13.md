# 14 Vulkan externs declared `-> bool` returned `Value::Int` in the interpreter

- **Status:** FIXED for the type mismatch; the Vulkan **benchmark** is still blocked (see below)
- **Found:** 2026-09-13, while trying to obtain a GPU offload before/after number

## The defect

`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl` declares 30 `rt_vulkan_*`
externs as `-> bool`. Fourteen of them returned `Value::Int(0/1)` from the
interpreter extern registry (`interpreter_extern/gpu.rs`) instead of
`Value::Bool`:

```
rt_vulkan_is_available      rt_vulkan_select_device     rt_vulkan_wait_idle
rt_vulkan_bind_buffer       rt_vulkan_bind_descriptors  rt_vulkan_bind_pipeline
rt_vulkan_dispatch          rt_vulkan_end_compute       rt_vulkan_submit_and_wait
rt_vulkan_wait_fence        rt_vulkan_destroy_fence     rt_vulkan_destroy_descriptor_set
rt_vulkan_dependency_quarantine_lock / _unlock
```

Their siblings (`rt_vulkan_init`, `rt_vulkan_shutdown`, …) already returned
`Value::Bool`, so this was an inconsistency, not a convention.

## Why it mattered

The idiomatic call form on the Vulkan path is `if not rt_vulkan_X():`. With an
`Int` payload under a `bool` declaration, that form **stops the caller dead**
instead of branching — no error, no diagnostic. Affected production sites
include the backend availability probe used by backend selection
(`ffi_vulkan.spl:125,307`, `sffi_vulkan.spl:396`) and
`vulkan_backend3d.spl:263`, plus the ENTIRE compute-dispatch surface
(`bind_pipeline` / `bind_descriptors` / `bind_buffer` / `dispatch` /
`end_compute` / `submit_and_wait` / `wait_fence`).

This is why `test/05_perf/graphics_2d/bench_2d_vulkan.spl` printed its banner
and then exited **0** with no frame timings on a host where Vulkan is in fact
present — it died at the first `if not rt_vulkan_is_available():`.

Observed before/after on the same host, same source:

```
before:  available=1      selected=1
after:   available=true   selected=true
```

## Fixed

All 14 now return `Value::Bool`, matching their declarations and their
siblings. Verified: Vulkan enumerates 1 device, `rt_vulkan_init()` succeeds,
`rt_vulkan_select_device(0)` returns `true`, and `rt_vulkan_alloc_buffer`
returns a live handle.

## Still blocked — the benchmark, for two further reasons

**1. Duplicate co-compiled `rt_vulkan_*` symbols.** A standalone spec that
declares the externs itself initialises Vulkan fine. `bench_2d_vulkan.spl`,
which pulls in `sffi_vulkan.*`, gets `rt_vulkan_init() == false` for the same
call on the same host. The run emits the repo's known
`compiler_cross_module_private_symbol_collision` warning class ("N co-compiled
definitions with differing signatures … a fallback hit may still dispatch to
the wrong one"). That dispatch ambiguity, not Vulkan, is what fails.

**2. `rt_vulkan_get_last_error()` yields nil** (`.len()` is `-1`), so
`print("FAIL: " + rt_vulkan_get_last_error())` dies mid-statement and the
benchmark's own failure path prints nothing. Every `FAIL:` branch in that file
is therefore silent.

**3. The host-to-device copy externs return false.** In the standalone spec,
`rt_vulkan_copy_to_buffer_array(buf, data, 65536, 0)` returns `false` on all 20
iterations (the 39 ms measured is call overhead, not transfer). So no genuine
GPU offload throughput number is obtainable in the interpreter lane on this
host yet.

## Consequence to state plainly

A Vulkan **frame-time** before/after comparison is not available. What can be
asserted about GPU offload is structural: no backend-selection, dynload,
`sffi_vulkan`, `ffi_vulkan`, `vulkan_icd`, `engine.spl` or `draw_ir.spl` file is
modified by the CPU/SIMD work, and the Vulkan boolean surface is now *more*
correct than before, not less.
