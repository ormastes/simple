# Vulkan instance init fails under `bin/simple run` but succeeds under `bin/simple test` (2026-08-25)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN. **Binary:** `bin/simple` = Rust seed (`bin/release/x86_64-unknown-linux-gnu/simple`).
**Host:** Linux, 2x NVIDIA (RTX A6000, TITAN RTX), `vulkaninfo` reports both at Vulkan 1.4.312.

## Symptom
Identical code — `VulkanLaneSession.create().probe()` then
`VulkanVmExecutor.create().init(<svmg_vulkan_kernel.spv bytes>)` and
`run_source("PUSHI 1\nPUSHI 9\nSYS_RESULT\nPUSHI 3\nSYS_EXIT", 1000, 0)`:

| path | probe() | init() | run |
|---|---|---|---|
| spec under `bin/simple test` (`examples/08_gpu/backends/backends_spec.spl`, and `test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl`) | `""` (live) | `""` | `ok=true exit=3 records=1` |
| program under `bin/simple run` (`examples/08_gpu/backends/svmg_hello.spl`, scratch probe) | `skip:vulkan-instance-init-failed` | same | — |
| `bin/simple run` with a probe session created first | live | `init` OK, then `vulkan-lane-pipeline-create-failed` | — |

`SIMPLE_EXECUTION_MODE=interpreter` on the run path does not change the outcome, and the
SPIR-V bytes are identical on both paths (`len=19068, b0..b3 = 3 2 35 7`), so this is not
`[u8]` corruption. CUDA through the same executor family works on BOTH paths
(`CudaVmExecutor`: `ok records=1 exit=3`).

## Where to look
- `rt_vulkan_init` (`src/compiler_rust/runtime/src/vulkan_graphics_runtime_core.rs:392`)
  → `VulkanInstance::get_or_init()`; the failure message is recorded via `state.set_error`
  and readable through `vulkan_sffi_last_error()` (`gpu/engine2d/sffi_vulkan.spl:806`).
  A scratch probe that printed it after `init()` produced no further output at all
  (process ended silently, rc=0) — that silent exit is itself suspicious.
- Difference candidates between the two entry paths: process environment/cwd the test
  runner sets for GPU lanes (`test_runner/test_executor_composite.spl:350-380`), or
  runtime state the `run` driver initialises before user code (a prior graphics/present
  init that leaves `VulkanInstance` in a failed state).

## Reproduce
```
cd examples/08_gpu/backends/vulkan && ../../../../bin/simple run ../svmg_hello.spl   # instance-init-failed
bin/simple test examples/08_gpu/backends/backends_spec.spl                            # vulkan case live-passes
```


## 2026-11-12 fix attempt — lane fix-runpath-gpu-20261112 (investigated, no in-scope fix)

Re-traced both entry paths on current HEAD (7a06b4aafd5):

- `simple run <file>` → `cli_handle_run` → `cli_run_file` → in-process
  `interpret_file` (no bootstrap driver is delegated to by default;
  `_cli_driver_binary()` returns ""). The CLI performs NO graphics/Vulkan
  initialization before user code — so the "prior present init leaves
  `VulkanInstance` in a failed state" suspect does not exist on the
  pure-Simple run path.
- `simple test` GPU lanes spawn a child `simple run
  src/app/test_runner_new/hosted_lane_main.spl --hosted-lane=gpu
  --gpu-lane=vulkan_vm`, which runs the executor in the same kind of
  in-process interpreter. The composite runner sets no Vulkan-relevant
  env/cwd for that child (`test_executor_composite.spl`,
  `test_executor_hosted_lanes.spl` contain no env_set/cwd manipulation).

So on the self-hosted tree, run and test share one interpreter route and
the measured run/test divergence was an artifact of the Rust seed binary
(`rt_vulkan_init` / `VulkanInstance::get_or_init`,
`src/compiler_rust/runtime/src/vulkan_graphics_runtime_core.rs:392`), which
is outside this lane's touch scope. The silent rc=0 exit when printing
`vulkan_sffi_last_error()` is the same extern-`text` return corruption as
`run_path_extern_text_corruption_causes_false_gpu_skip_2026-08-20`
(extern `text` returns across the run-path JIT/native route).

No source change made (nothing in the lane's scope can affect the seed's
runtime init order). The underlying extern-`text` ABI fix belongs to the
compiler-core lane owning `50.mir`/`70.backend`.

Verification pending: re-run of `examples/08_gpu/backends/svmg_hello.spl`
under `simple run` on a Vulkan host once the admitted compiler exists.

Status: OPEN (root cause identified; fix site out of lane scope).
