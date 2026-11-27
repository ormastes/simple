# Stage2 runtime missing `rt_heap_aux_live_bytes` (2026-11-02)

Status: FIXED (branch work/runtime-completeness-20261102)

## Symptom

The phase-3 manual stage3 link failed: `rt_heap_aux_live_bytes` was declared
`extern fn` in `src/lib/nogc_sync_mut/sffi/host.spl` (and in
`src/compiler/80.driver/driver_worker_surface_closure_v1.spl`,
`src/app/cli/native_build_worker.spl`), but no runtime C file defined it. Only
the Rust runtime (`value/heap.rs`) had it. A tagged local shim returning 0 was
used to finish the bootstrap link. `rt_heap_array_capacity_bytes` had the
same gap.

The same link also needed C owners that the baked core-C runtime list
(`runtime_core_c_sources_v1`) omitted: `runtime_cranelift_bridge_stub.c`,
`platform/async_driver.c`, `platform/async_windows.c`
(`runtime_process_tree.c` was already listed).

## Fix

- `runtime_native.c`: real aux-byte accounting. Relaxed atomic counters are
  updated at every array element-buffer and dict entry-table allocate,
  realloc, and free site. `rt_heap_aux_live_bytes` returns array plus dict
  backing bytes, and `rt_heap_array_capacity_bytes` returns the array subset,
  matching the Rust contract.
- `runtime_compiler.spl`: the core-C list now includes
  `runtime_cranelift_bridge_stub`, and on Windows targets it includes
  `platform/async_driver` and `platform/async_windows` through
  `runtime_core_c_platform_sources_v1`. Object basenames are flattened
  (`platform/x` becomes `platform_x`).
- New gate: `scripts/check/check-runtime-link-completeness.shs`, with spec
  `test/02_integration/runtime/runtime_link_completeness_spec.spl`.

## Tests (each failed before the change)

- `src/runtime/test/rt_heap_aux_live_bytes_selfcheck.c`: before the fix the
  link failed with `undefined symbol: rt_heap_aux_live_bytes` and
  `rt_heap_array_capacity_bytes`.
- `check-runtime-link-completeness.shs` on the pre-fix tree:
  `MISSING rt_heap_array_capacity_bytes`, `MISSING rt_heap_aux_live_bytes`,
  `STATUS: FAIL`.
- `runtime_source_list_completeness_spec.spl` on the pre-fix list: 4 of 5
  examples failed.

## Follow-up

The tagged 0-returning shim in the phase-3 run can be removed once this lands.
