# VulkanVmExecutor returns ok=true / exit=0 / 0 records when run after a CUDA lane in the same process (2026-08-25)

**Status:** OPEN — `examples/08_gpu/backends/backends_spec.spl` is deliberately RED on this host
(`Results: 4 total, 3 passed, 1 failed, 1 skipped`), per the "correct spec that fails" rule.
**Binary:** Rust seed. **Host:** Linux, 2x NVIDIA, Vulkan 1.4.312 live.

## Evidence
Same program `PUSHI 1\nPUSHI 9\nSYS_RESULT\nPUSHI 3\nSYS_EXIT`, same `VulkanVmExecutor.create()` +
`init(svmg_vulkan_kernel.spv)` + `run_source(.., 1000, 0)`:

| process content | outcome |
|---|---|
| Vulkan case alone (scratch spec, `bin/simple test`) | `ok=true exit=3 records=1` (value 9) |
| `test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl` (Vulkan only) | `2 total, 2 passed` |
| `backends_spec.spl`: CUDA case (live, `exit=3`, 1 record) **then** Vulkan case | Vulkan: `ok=true`, **`exit=0`, `records.len()=0`** — `assert_equal failed: expected 3, got 0` |

`ok=true` with no sentinel and no records means the dispatch "succeeded" without the program's
effects reaching the mailbox — i.e. a silent wrong answer, not a skip. Every existing gpu_lane
conformance spec is single-backend per process, so this interference has no coverage today.

## Suspects
- Shared per-process state between `CudaLaneSession` / `VulkanLaneSession` — the GMB-1 mailbox
  arena or its sentinel/reader cursor (`std.nogc_sync_mut.test_runner.gpu_mailbox`), consumed by
  the first lane and not re-armed for the second.
- `vulkan_sffi_shutdown_reaped()` / CUDA context teardown ordering in the lane sessions.

## Unblock
Either fix the shared state so both lanes run in one process, or make the second lane FAIL
loudly (never `ok=true exit=0`). Keep `backends_spec.spl` strict; it goes green when fixed.
Related (different symptom, same area):
`doc/08_tracking/bug/vulkan_instance_init_fails_under_run_but_not_test_2026-08-25.md`.
