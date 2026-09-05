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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce for Gap A (2026-08-25): the example imported cuda_get_device_name,
CudaStream and stream helpers from std.cuda and none existed (E1002).
Both families that back `std.cuda` must expose them.

## Scenarios

### std.cuda surface (device-free)

#### exposes streams in both backing families

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes streams in both backing families
   - Expected: stream.is_valid equals `cuda_available()`
   - Expected: stream.handle > 0 equals `cuda_available()`
   - Expected: cuda_default_stream().handle equals `0`
   - Expected: cuda_stream_destroy(stream) is true
   - Expected: async_stream.handle > 0 equals `cuda_available()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes streams in both backing families")
val stream = cuda_stream_create()
expect(stream.is_valid).to_equal(cuda_available())
# plan E2: create() now returns a real driver stream (handle > 0) when a
# driver is present; the null stream is cuda_default_stream() (handle 0).
expect(stream.handle > 0).to_equal(cuda_available())
expect(cuda_default_stream().handle).to_equal(0)
expect(cuda_stream_destroy(stream)).to_equal(true)
val async_stream = async_stream_create()
expect(async_stream.handle > 0).to_equal(cuda_available())
```

</details>

#### exposes cuda_get_device_name by ordinal

- exposes cuda_get_device_name by ordinal
   - Expected: cuda_get_device_name(0) equals `cuda_device_name(cuda_device_get(0))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes cuda_get_device_name by ordinal")
# No device: both must answer the same thing rather than crash.
if not cuda_available():
    expect(cuda_get_device_name(0)).to_equal(cuda_device_name(cuda_device_get(0)))
```

</details>

### std.cuda surface on hardware

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

#### names device 0 through both families

- names device 0 through both families
   - Expected: name equals `cuda_device_name(cuda_device_get(0))`
   - Expected: async_get_device_name(0) equals `name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("names device 0 through both families")
val name = cuda_get_device_name(0)
expect(name.len()).to_be_greater_than(0)
expect(name).to_equal(cuda_device_name(cuda_device_get(0)))
expect(async_get_device_name(0)).to_equal(name)
```

</details>

#### synchronises the default stream

- synchronises the default stream
   - Expected: cuda_init() equals `0`
   - Expected: cuda_ctx_create(cuda_device_get(0)) > 0 is true
   - Expected: stream.is_valid is true
   - Expected: cuda_stream_sync(stream) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("synchronises the default stream")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e4329c60e2059764d9ba487626a1f10e219f11342f0e02a82d8da07218c7bd33`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4329c60e2059764d9ba487626a1f10e219f11342f0e02a82d8da07218c7bd33`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4329c60e2059764d9ba487626a1f10e219f11342f0e02a82d8da07218c7bd33`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gpu/cuda_public_surface_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/cuda_public_surface_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/cuda_public_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/cuda_public_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/cuda_public_surface_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/cuda_public_surface_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes streams in both backing families' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/cuda_public_surface_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes cuda_get_device_name by ordinal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/cuda_public_surface_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: CUDA not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
