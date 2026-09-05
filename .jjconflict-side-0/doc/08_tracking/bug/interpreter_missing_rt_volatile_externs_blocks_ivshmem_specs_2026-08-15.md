# Interpreter has no rt_volatile_read/write_* externs — every ivshmem lane untestable under `simple test`

**Date:** 2026-08-15
**Status:** OPEN
**Severity:** P3 — coverage/testability gap: host-gpu ivshmem code paths
cannot be exercised by any spec on the tree-walk interpreter

## Symptom

Any spec that touches an ivshmem/mmio region via `rt_volatile_read_*` /
`rt_volatile_write_*` fails with `semantic: unknown extern function` under
`bin/simple test` (tree-walk interpreter). The symbols exist only in the
JIT/native table (src/compiler_rust/common/src/runtime_symbols.rs:779-786).

Discovered while driving branch coverage of
src/os/compositor/engine2d_wm_frame_executor.spl: a full rt_alloc
mock-ivshmem region + OS-thread mock host was built, but every
`_render_host_gpu` lane is unreachable — capping that module at 62% (23/37
decisions) headless. See
test/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.spl
docstring for the per-line catalogue.

## Unblock

Register interpreter handlers for the rt_volatile_* family (plain loads/
stores suffice for hosted mock regions), then extend the executor spec's
host-gpu waves.
