# device_detect_spec

> GPU Device Detection Specification (Updated)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# device_detect_spec

GPU Device Detection Specification (Updated)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gpu/engine2d/device_detect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

GPU Device Detection Specification (Updated)

@tag: gpu, device, detection, backend
NO COVERAGE CLAIMED. Stream F4 (2026-08-09) removed the
`@cover src/lib/gc_async_mut/gpu/device.spl 80%` claim that stood here: all 14 `it` bodies are the single gate assertion, and the file never
references detect_backends or preferred_backend. Coverage was 0%, not 80%.
The subject (a 4-line facade re-exporting std.common.gpu.device and
std.nogc_sync_mut.gpu.device) does resolve correctly, unlike the
engine2d/ffi_* facades.
See doc/08_tracking/bug/gated_specs_are_tautology_shells_2026-08-09.md
and doc/08_tracking/bug/gc_async_mut_gpu_ffi_facades_are_dangling_2026-08-09.md.

Verifies GpuBackend enum expansion, detect_backends_full with FfiMode,
and per-platform detection. Covers AC-1 through AC-5, AC-7, AC-8.

## Scenarios

### GpuBackend

#### AC-5: has Qualcomm variant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-5: has Qualcomm variant
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: has Qualcomm variant")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-1: has Vulkan variant

- AC-1: has Vulkan variant
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: has Vulkan variant")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-2: has Cuda variant

- AC-2: has Cuda variant
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: has Cuda variant")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-3: has Rocm variant

- AC-3: has Rocm variant
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: has Rocm variant")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: has OneApi variant

- AC-4: has OneApi variant
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: has OneApi variant")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### has None_ variant for CPU fallback

- has None_ variant for CPU fallback
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has None_ variant for CPU fallback")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### detect_backends_full

#### AC-8: accepts GpuFfiMode parameter

- AC-8: accepts GpuFfiMode parameter
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: accepts GpuFfiMode parameter")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-8: Static mode checks extern fn availability

- AC-8: Static mode checks extern fn availability
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: Static mode checks extern fn availability")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-8: Dynamic mode checks dlopen availability

- AC-8: Dynamic mode checks dlopen availability
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: Dynamic mode checks dlopen availability")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-1: Vulkan detection enabled (not commented out)

- AC-1: Vulkan detection enabled (not commented out)
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: Vulkan detection enabled (not commented out)")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-3: ROCm detection enabled

- AC-3: ROCm detection enabled
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: ROCm detection enabled")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: Intel detection enabled

- AC-4: Intel detection enabled
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: Intel detection enabled")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### detect_best_backend_for_platform

#### AC-7: returns a valid backend name

- AC-7: returns a valid backend name
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: returns a valid backend name")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

<details>
<summary>Advanced: AC-7: priority order matches platform matrix</summary>

#### AC-7: priority order matches platform matrix

- AC-7: priority order matches platform matrix
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: priority order matches platform matrix")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `ac4c38d5c60acecb0d73b8aeff9de3e16d37685ee2c15265df5894421ff34294`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac4c38d5c60acecb0d73b8aeff9de3e16d37685ee2c15265df5894421ff34294`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac4c38d5c60acecb0d73b8aeff9de3e16d37685ee2c15265df5894421ff34294`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gpu/engine2d/device_detect_spec.spl
mirror: doc/06_spec/unit/lib/gpu/engine2d/device_detect_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gpu/engine2d/device_detect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gpu/engine2d/device_detect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gpu/engine2d/device_detect_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: has Qualcomm variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine2d/device_detect_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: has Vulkan variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine2d/device_detect_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: has Cuda variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
