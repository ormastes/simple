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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce for the 12.First_Kernel SEGV (2026-08-25): gpu_upload_* /
gpu_download_* in src/lib/gc_async_mut/gpu_ops.spl passed
`array.data_ptr()` — the interpreter's tagged Value buffer — as raw element
bytes, so uploads sent garbage and downloads memcpy'd over Value tags
(SEGV at 2048 elements, silent corruption below). Hardware only.

## Scenarios

### std.gpu typed transfers on hardware

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### round-trips 2048 f32 values (the SEGV size)

- round-trips 2048 f32 values (the SEGV size)
   - Expected: gpu_init().is_ok() is true
   - Expected: gpu_set_device(0).is_ok() is true
   - Expected: gpu_upload_f32(buf, data).is_ok() is true
   - Expected: back.len() equals `n`
   - Expected: back[0] equals `0.0`
   - Expected: back[1] equals `0.5`
   - Expected: back[2047] equals `1023.5`
   - Expected: gpu_free(buf).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips 2048 f32 values (the SEGV size)")
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

- keeps the sign bit of negative f32 values
   - Expected: gpu_upload_f32(buf, data).is_ok() is true
   - Expected: gpu_download_f32(buf, 4).unwrap() equals `data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the sign bit of negative f32 values")
val data = [-1.5, -0.25, 3.0, -1024.0] as [f32]
val buf = gpu_alloc(16).unwrap()
expect(gpu_upload_f32(buf, data).is_ok()).to_equal(true)
expect(gpu_download_f32(buf, 4).unwrap()).to_equal(data)
gpu_free(buf)
```

</details>

#### round-trips negative i32 values

- round-trips negative i32 values
   - Expected: gpu_upload_i32(buf, data).is_ok() is true
   - Expected: gpu_download_i32(buf, 4).unwrap() equals `data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips negative i32 values")
val data = [-1, -2147483648, 2147483647, 7] as [i32]
val buf = gpu_alloc(16).unwrap()
expect(gpu_upload_i32(buf, data).is_ok()).to_equal(true)
expect(gpu_download_i32(buf, 4).unwrap()).to_equal(data)
gpu_free(buf)
```

</details>

#### round-trips i64 values

- round-trips i64 values
   - Expected: gpu_upload_i64(buf, data).is_ok() is true
   - Expected: gpu_download_i64(buf, 4).unwrap() equals `data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips i64 values")
val data = [-1, 1 << 40, -(1 << 50), 0]
val buf = gpu_alloc(32).unwrap()
expect(gpu_upload_i64(buf, data).is_ok()).to_equal(true)
expect(gpu_download_i64(buf, 4).unwrap()).to_equal(data)
gpu_free(buf)
```

</details>

#### round-trips f64 values

- round-trips f64 values
   - Expected: gpu_upload_f64(buf, data).is_ok() is true
   - Expected: gpu_download_f64(buf, 4).unwrap() equals `data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips f64 values")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c935bf2d30759dc85a2b79a5b06e62684fc63c5d79f7d167178924a2f1c9ffaf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c935bf2d30759dc85a2b79a5b06e62684fc63c5d79f7d167178924a2f1c9ffaf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c935bf2d30759dc85a2b79a5b06e62684fc63c5d79f7d167178924a2f1c9ffaf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gpu/gpu_ops_typed_transfer_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/gpu_ops_typed_transfer_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/gpu_ops_typed_transfer_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/gpu_ops_typed_transfer_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/gpu_ops_typed_transfer_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/gpu_ops_typed_transfer_roundtrip_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: CUDA not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/gpu_ops_typed_transfer_roundtrip_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips 2048 f32 values (the SEGV size)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/gpu_ops_typed_transfer_roundtrip_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the sign bit of negative f32 values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
