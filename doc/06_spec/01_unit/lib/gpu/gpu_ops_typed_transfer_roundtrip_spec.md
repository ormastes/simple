# std.gpu typed upload/download round-trips real element bytes

> Reproduce for the 12.First_Kernel SEGV (2026-08-25): gpu_upload_* /

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# std.gpu typed upload/download round-trips real element bytes

Reproduce for the 12.First_Kernel SEGV (2026-08-25): gpu_upload_* /

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/gpu_ops_typed_transfer_roundtrip_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce for the 12.First_Kernel SEGV (2026-08-25): gpu_upload_* /
gpu_download_* in src/lib/gc_async_mut/gpu_ops.spl passed
`array.data_ptr()` — the interpreter's tagged Value buffer — as raw element
bytes, so uploads sent garbage and downloads memcpy'd over Value tags
(SEGV at 2048 elements, silent corruption below). Hardware only.

## Scenarios

### std.gpu typed transfers on hardware

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

#### round-trips 2048 f32 values (the SEGV size)

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gpu_init().is_ok()).to_equal(true)
expect(gpu_set_device(0).is_ok()).to_equal(true)
val n = 2048
val data = [for i in 0..n: (i as f32) * 0.5]
val buf = gpu_alloc(n * 4).unwrap()
expect(gpu_upload_f32(buf, data).is_ok()).to_equal(true)
val back = gpu_download_f32(buf, n).unwrap()
expect(back.len()).to_equal(n)
expect(back[0]).to_equal(0.0)
expect(back[1]).to_equal(0.5)
expect(back[2047]).to_equal(1023.5)
expect(gpu_free(buf).is_ok()).to_equal(true)
```

</details>

#### keeps the sign bit of negative f32 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [-1.5, -0.25, 3.0, -1024.0] as [f32]
val buf = gpu_alloc(16).unwrap()
expect(gpu_upload_f32(buf, data).is_ok()).to_equal(true)
expect(gpu_download_f32(buf, 4).unwrap()).to_equal(data)
gpu_free(buf)
```

</details>

#### round-trips negative i32 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [-1, -2147483648, 2147483647, 7] as [i32]
val buf = gpu_alloc(16).unwrap()
expect(gpu_upload_i32(buf, data).is_ok()).to_equal(true)
expect(gpu_download_i32(buf, 4).unwrap()).to_equal(data)
gpu_free(buf)
```

</details>

#### round-trips i64 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [-1, 1 << 40, -(1 << 50), 0]
val buf = gpu_alloc(32).unwrap()
expect(gpu_upload_i64(buf, data).is_ok()).to_equal(true)
expect(gpu_download_i64(buf, 4).unwrap()).to_equal(data)
gpu_free(buf)
```

</details>

#### round-trips f64 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [-2.5, 1.0e300, 3.141592653589793, -0.0]
val buf = gpu_alloc(32).unwrap()
expect(gpu_upload_f64(buf, data).is_ok()).to_equal(true)
expect(gpu_download_f64(buf, 4).unwrap()).to_equal(data)
gpu_free(buf)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
