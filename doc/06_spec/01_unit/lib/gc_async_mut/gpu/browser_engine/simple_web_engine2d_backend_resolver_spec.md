# Simple Web Engine2d Backend Resolver Specification

> Tests covering Simple Web Engine2D backend resolver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Engine2d Backend Resolver Specification

## Scenarios

### Simple Web Engine2D backend resolver

#### routes auto through viability-gated detection

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes auto through viability-gated detection
   - Expected: simple_web_engine2d_resolved_backend_name(40, 24, "auto") equals `Engine2D.detect_best_backend_viable()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes auto through viability-gated detection")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "auto")).to_equal(Engine2D.detect_best_backend_viable())
```

</details>

#### auto never selects a GPU backend that fails its viability probe

- auto never selects a GPU backend that fails its viability probe
   - Expected: chosen_probe.status == BackendStatus.Initialized is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto never selects a GPU backend that fails its viability probe")
val chosen = simple_web_engine2d_resolved_backend_name(40, 24, "auto")
val chosen_probe = Engine2D.probe_backend_viable(chosen)
expect(chosen_probe.status == BackendStatus.Initialized).to_equal(true)
```

</details>

#### auto skips a shallow-available candidate whose deep probe fails

- auto skips a shallow-available candidate whose deep probe fails
   - Expected: deep.status == BackendStatus.Initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto skips a shallow-available candidate whose deep probe fails")
val chosen = simple_web_engine2d_resolved_backend_name(40, 24, "auto")
val order = backend_default_priority_order()
var idx = 0
val order_len = order.len()
while idx < order_len:
    val name = order[idx]
    if name == chosen:
        idx = order_len
    else:
        # Every candidate preferred over the chosen one must be
        # genuinely non-viable (shallow-unavailable OR deep-rejected).
        val deep = Engine2D.probe_backend_viable(name)
        expect(deep.status == BackendStatus.Initialized).to_equal(false)
        idx = idx + 1
```

</details>

#### preserves DirectX backend requests and UI aliases

- preserves DirectX backend requests and UI aliases
   - Expected: simple_web_engine2d_resolved_backend_name(40, 24, "directx") equals `expected`
   - Expected: simple_web_engine2d_resolved_backend_name(40, 24, "d3d11") equals `expected`
   - Expected: simple_web_engine2d_resolved_backend_name(40, 24, "dx11") equals `expected`
   - Expected: simple_web_engine2d_resolved_backend_name(40, 24, "dx12") equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves DirectX backend requests and UI aliases")
val expected = resolved_or_software(40, 24, "directx")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "directx")).to_equal(expected)
expect(simple_web_engine2d_resolved_backend_name(40, 24, "d3d11")).to_equal(expected)
expect(simple_web_engine2d_resolved_backend_name(40, 24, "dx11")).to_equal(expected)
expect(simple_web_engine2d_resolved_backend_name(40, 24, "dx12")).to_equal(expected)
```

</details>

#### preserves shared HIP and CPU SIMD aliases

- preserves shared HIP and CPU SIMD aliases
   - Expected: simple_web_engine2d_resolved_backend_name(40, 24, "hip") equals `resolved_or_software(40, 24, "hip")`
   - Expected: simple_web_engine2d_resolved_backend_name(40, 24, "amd-rocm") equals `resolved_or_software(40, 24, "amd-rocm")`
   - Expected: simple_web_engine2d_resolved_backend_name(40, 24, "simd-cpu") equals `resolved_or_software(40, 24, "simd-cpu")`
   - Expected: simple_web_engine2d_resolved_backend_name(40, 24, "cpu-simd") equals `resolved_or_software(40, 24, "cpu-simd")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves shared HIP and CPU SIMD aliases")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "hip")).to_equal(resolved_or_software(40, 24, "hip"))
expect(simple_web_engine2d_resolved_backend_name(40, 24, "amd-rocm")).to_equal(resolved_or_software(40, 24, "amd-rocm"))
expect(simple_web_engine2d_resolved_backend_name(40, 24, "simd-cpu")).to_equal(resolved_or_software(40, 24, "simd-cpu"))
expect(simple_web_engine2d_resolved_backend_name(40, 24, "cpu-simd")).to_equal(resolved_or_software(40, 24, "cpu-simd"))
```

</details>

#### still falls back unknown backend names to deterministic software

- still falls back unknown backend names to deterministic software
   - Expected: simple_web_engine2d_resolved_backend_name(40, 24, "unknown-directx-like") equals `software`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still falls back unknown backend names to deterministic software")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "unknown-directx-like")).to_equal("software")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple Web Engine2D backend resolver.
- Simple Web Engine2D backend resolver

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0e14b23c073aae35b3499fcf4284530882a0b366678896c9f28c95ed3ab187a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e14b23c073aae35b3499fcf4284530882a0b366678896c9f28c95ed3ab187a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e14b23c073aae35b3499fcf4284530882a0b366678896c9f28c95ed3ab187a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes auto through viability-gated detection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'auto never selects a GPU backend that fails its viability probe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'auto skips a shallow-available candidate whose deep probe fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
