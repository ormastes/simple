# backends_spec

> Purpose: prove the same SVM-G program runs on cuda / vulkan / metal with only

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backends_spec

Purpose: prove the same SVM-G program runs on cuda / vulkan / metal with only

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `examples/08_gpu/backends/backends_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose: prove the same SVM-G program runs on cuda / vulkan / metal with only
the per-directory `simple.sdn` `gpu:` section changing (examples/08_gpu/backends/).
Audience: GPU backend and example maintainers.
Run: bin/simple test examples/08_gpu/backends/backends_spec.spl   (from repo root)

## Scenarios

### examples/08_gpu/backends — one program, three simple.sdn configs

#### each directory's simple.sdn selects exactly its own backend

- Parse the three checked-in manifests


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse the three checked-in manifests")
for b in ["cuda", "vulkan", "metal"]:
    val cfg = load_gpu_config("{CONFIG_DIR}/{b}/simple.sdn")
    assert_equal(cfg.backend, b)
    assert_equal(cfg.submode, "interpreter")
```

</details>

#### cuda config: runs the program on a live CUDA device, or SKIPs with the lane's own reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = CudaLaneSession.create().probe()
if probe.starts_with("skip:"):
    gpu_lane_report_skip("backends example cuda", probe)
    assert_equal(gpu_lane_probe_verdict("cuda", probe), "skip")
else:
    var ex = CudaVmExecutor.create()
    assert_equal(ex.init(file_read_bytes("{LANE_DIR}/svmg_cuda_kernel.ptx")), "")
    val o = ex.run_source(HELLO_PROGRAM, 1000, 0)
    assert_true(o.ok)
    assert_equal(o.exit_code, 3)
    assert_equal(o.records.len(), 1)
    assert_equal(o.records[0].value, 9)
```

</details>

#### vulkan config: runs the same program on a live Vulkan device, or SKIPs with the lane's own reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = VulkanLaneSession.create().probe()
if probe.starts_with("skip:"):
    gpu_lane_report_skip("backends example vulkan", probe)
    assert_equal(gpu_lane_probe_verdict("vulkan", probe), "skip")
else:
    var ex = VulkanVmExecutor.create()
    assert_equal(ex.init(file_read_bytes("{LANE_DIR}/svmg_vulkan_kernel.spv")), "")
    val o = ex.run_source(HELLO_PROGRAM, 1000, 0)
    assert_true(o.ok)
    assert_equal(o.exit_code, 3)
    # KNOWN RED on a host where the cuda case above ran live first:
    # doc/08_tracking/bug/vulkan_vm_lane_returns_exit0_after_cuda_lane_same_process_2026-08-25.md
    assert_equal(o.records.len(), 1)
    assert_equal(o.records[0].value, 9)
```

</details>

#### metal config: runs on macOS, and on any other host reports the honest skip reason (never a fake pass)

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = MetalLaneSession.create().probe()
if probe.starts_with("skip:"):
    gpu_lane_report_skip("backends example metal", probe)
    assert_equal(gpu_lane_probe_verdict("metal", probe), "skip")
    assert_true(probe.starts_with("skip:metal-unavailable"))
else:
    var ex = MetalVmExecutor.create()
    assert_equal(ex.init(file_read_text("{LANE_DIR}/svmg_metal_kernel.metal")), "")
    val o = ex.run_source(HELLO_PROGRAM, 1000, 0)
    assert_true(o.ok)
    assert_equal(o.exit_code, 3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
