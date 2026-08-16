# Interpreter has no rt_volatile_read/write_* externs — every ivshmem lane untestable under `simple test`

**Date:** 2026-08-15
**Status:** RESOLVED (2026-08-16)
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

## Resolution (2026-08-16)

All 8 handlers implemented in
`src/compiler_rust/compiler/src/interpreter_extern/memory.rs` (family
`rt_volatile_read_u{8,16,32,64}(addr) -> i64` /
`rt_volatile_write_u{8,16,32,64}(addr, value)`, matching the native
signatures at runtime/src/lib.rs:379-417) and registered in
`interpreter_extern/mod.rs` next to the `rt_mmio_*` entries. Addresses are
treated as plain process-memory addresses (mock ivshmem = `rt_alloc` buffer),
using `read_volatile`/`write_volatile` to mirror the JIT lane.

Evidence (seed rebuilt via `cargo build --release --bin simple`, `cargo
check` clean):
- Before (deployed binary): probe spec fails
  `semantic: unknown extern function: rt_volatile_write_u8`, exit 1.
- After (`target/release/simple test` on an 8-op u8/u16/u32/u64 round-trip
  probe): `Results: 1 total, 1 passed, 0 failed`, exit 0.
- `wm_frame_executor_branch_coverage_spec.spl` now executes (no
  unknown-extern crash anywhere in its 2012-line log); it currently exceeds
  the test-daemon 120s worker budget — a separate perf concern for that
  heavy spec, not an extern gap.
