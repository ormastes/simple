# std.gpu_runtime backend detection uses the CUDA driver probe

> Reproduce for Gap D (2026-08-25): gpu_available / gpu_backend_name /

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# std.gpu_runtime backend detection uses the CUDA driver probe

Reproduce for Gap D (2026-08-25): gpu_available / gpu_backend_name /

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/gpu_runtime_backend_probe_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce for Gap D (2026-08-25): gpu_available / gpu_backend_name /
gpu_device_count in src/lib/nogc_sync_mut/gpu_runtime/mod.spl gated on
rt_torch_cuda_available, so a host with two real GPUs and no PyTorch runtime
reported "CPU" and 0 devices while std.cuda counted 2.

## Scenarios

### std.gpu_runtime backend detection (device-free)

#### does not gate device detection on the torch runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file(OWNER)
for name in ["gpu_available", "gpu_backend_name", "gpu_device_count"]:
    expect(body_of(source, name).contains("rt_torch_cuda_available")).to_equal(false)
```

</details>

#### agrees with the std.cuda driver probe

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_available()).to_equal(cuda_available())
expect(gpu_device_count() as i64).to_equal(cuda_device_count())
if cuda_available():
    expect(gpu_backend_name()).to_equal("CUDA")
else:
    expect(gpu_backend_name()).to_equal("CPU")
```

</details>

### std.gpu_runtime backend detection on hardware

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### counts the real devices

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_available()).to_equal(true)
expect(gpu_backend_name()).to_equal("CUDA")
expect(gpu_device_count() as i64).to_be_greater_than(0)
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
