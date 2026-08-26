# std.cuda public surface used by examples/08_gpu/cuda/basic.spl

> Reproduce for Gap A (2026-08-25): the example imported cuda_get_device_name,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# std.cuda public surface used by examples/08_gpu/cuda/basic.spl

Reproduce for Gap A (2026-08-25): the example imported cuda_get_device_name,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/cuda_public_surface_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce for Gap A (2026-08-25): the example imported cuda_get_device_name,
CudaStream and stream helpers from std.cuda and none existed (E1002).
Both families that back `std.cuda` must expose them.

## Scenarios

### std.cuda surface (device-free)

#### exposes streams in both backing families

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stream = cuda_stream_create()
expect(stream.is_valid).to_equal(cuda_available())
expect(stream.handle).to_equal(0)
expect(cuda_stream_destroy(stream)).to_equal(true)
val async_stream = async_stream_create()
expect(async_stream.handle).to_equal(0)
```

</details>

#### exposes cuda_get_device_name by ordinal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# No device: both must answer the same thing rather than crash.
if not cuda_available():
    expect(cuda_get_device_name(0)).to_equal(cuda_device_name(cuda_device_get(0)))
```

</details>

### std.cuda surface on hardware

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

#### names device 0 through both families

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = cuda_get_device_name(0)
expect(name.len()).to_be_greater_than(0)
expect(name).to_equal(cuda_device_name(cuda_device_get(0)))
expect(async_get_device_name(0)).to_equal(name)
```

</details>

#### synchronises the default stream

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cuda_init()).to_equal(0)
expect(cuda_ctx_create(cuda_device_get(0)) > 0).to_equal(true)
val stream = cuda_stream_create()
expect(stream.is_valid).to_equal(true)
expect(cuda_stream_sync(stream)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
