# cuda_module_resource_wrapper_spec

> Resource wrapper for CudaModule — WP-J pilot migration

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cuda_module_resource_wrapper_spec

Resource wrapper for CudaModule — WP-J pilot migration

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/cuda_module_resource_wrapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

```simple
Resource wrapper for CudaModule — WP-J pilot migration

Tests the CudaModule wrapper class with resource ownership pattern:
- Sentinel-based validity checks (handle > 0 valid; 0 = closed sentinel;
  negative = load-failure error code, never a live handle)
- Consuming close() method
- Double-close guard (one-shot safety)
- Borrow methods refuse to touch an invalid handle

NOTE: close()/get_function on a VALID-looking fabricated handle are
deliberately NOT tested — they call real C externs (rt_cuda_module_unload
etc.) on a bogus pointer, which is undefined behavior and previously
crashed the test runner in the Image wrapper spec. All guard proofs below
use std.spec.step

use only invalid sentinels (0 and negative), which short-circuit before
any extern call.

```
## Scenarios

### CudaModule resource wrapper

#### is_valid accepts a positive handle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is_valid accepts a positive handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_valid accepts a positive handle")
val m = CudaModule(handle: 42)
assert_true(m.is_valid())
```

</details>

#### is_valid detects the closed sentinel (0)

- is_valid detects the closed sentinel (0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_valid detects the closed sentinel (0)")
val m = CudaModule(handle: 0)
assert_false(m.is_valid())
```

</details>

#### is_valid rejects negative error-code values

- is_valid rejects negative error-code values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_valid rejects negative error-code values")
val m = CudaModule(handle: -3)
assert_false(m.is_valid())
```

</details>

#### close on closed sentinel is safe and idempotent

- close on closed sentinel is safe and idempotent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close on closed sentinel is safe and idempotent")
val m = CudaModule(handle: 0)
m.close()
assert_equal(m.handle, 0)
m.close()
assert_equal(m.handle, 0)
```

</details>

#### close on negative error-code handle never calls unload

- close on negative error-code handle never calls unload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close on negative error-code handle never calls unload")
val m = CudaModule(handle: -1)
m.close()
assert_equal(m.handle, -1)
```

</details>

#### get_function refuses an invalid handle

- get_function refuses an invalid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_function refuses an invalid handle")
val m = CudaModule(handle: 0)
assert_equal(m.get_function("kernel_main"), 0)
```

</details>

#### load from nonexistent path returns nil

- load from nonexistent path returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("load from nonexistent path returns nil")
val result = cuda_module_load_resource("/nonexistent/module.ptx")
assert_nil(result)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `a39e3d2a5079170e956573a441a90d3908a1522b82fd9829d7aa8ba524fced44`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a39e3d2a5079170e956573a441a90d3908a1522b82fd9829d7aa8ba524fced44`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a39e3d2a5079170e956573a441a90d3908a1522b82fd9829d7aa8ba524fced44`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/gpu/cuda_module_resource_wrapper_spec.spl
mirror: doc/06_spec/01_unit/gpu/cuda_module_resource_wrapper_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/gpu/cuda_module_resource_wrapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/gpu/cuda_module_resource_wrapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/gpu/cuda_module_resource_wrapper_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_valid accepts a positive handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/gpu/cuda_module_resource_wrapper_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_valid detects the closed sentinel (0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/gpu/cuda_module_resource_wrapper_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_valid rejects negative error-code values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
