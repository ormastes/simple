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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce for Gap D (2026-08-25): gpu_available / gpu_backend_name /
gpu_device_count in src/lib/nogc_sync_mut/gpu_runtime/mod.spl gated on
rt_torch_cuda_available, so a host with two real GPUs and no PyTorch runtime
reported "CPU" and 0 devices while std.cuda counted 2.

## Scenarios

### std.gpu_runtime backend detection (device-free)

#### does not gate device detection on the torch runtime

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not gate device detection on the torch runtime
   - Expected: body_of(source, name) does not contain `rt_torch_cuda_available`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not gate device detection on the torch runtime")
val source = read_file(OWNER)
for name in ["gpu_available", "gpu_backend_name", "gpu_device_count"]:
    expect(body_of(source, name).contains("rt_torch_cuda_available")).to_equal(false)
```

</details>

#### agrees with the std.cuda driver probe

- agrees with the std.cuda driver probe
   - Expected: gpu_available() equals `cuda_available()`
   - Expected: gpu_device_count() as i64 equals `cuda_device_count()`
   - Expected: gpu_backend_name() equals `CUDA`
   - Expected: gpu_backend_name() equals `CPU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with the std.cuda driver probe")
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

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### counts the real devices

- counts the real devices
   - Expected: gpu_available() is true
   - Expected: gpu_backend_name() equals `CUDA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts the real devices")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a0e29310493e2fff603852ac40cf0500986d4d7fe954e04c016a907115f2310c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0e29310493e2fff603852ac40cf0500986d4d7fe954e04c016a907115f2310c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0e29310493e2fff603852ac40cf0500986d4d7fe954e04c016a907115f2310c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/gpu_runtime_backend_probe_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/gpu_runtime_backend_probe_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/gpu_runtime_backend_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/gpu_runtime_backend_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/gpu_runtime_backend_probe_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not gate device detection on the torch runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/gpu_runtime_backend_probe_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with the std.cuda driver probe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/gpu_runtime_backend_probe_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: CUDA not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
