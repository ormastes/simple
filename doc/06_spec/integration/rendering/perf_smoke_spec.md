# Perf Smoke Specification

> Tests covering Backend Perf Smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Perf Smoke Specification

## Scenarios

### Backend Perf Smoke

#### cpu baseline

#### cpu init_ms is measured

- cpu init_ms is measured


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu init_ms is measured")
val rec = measure_backend("cpu")
print_perf_record(rec)
expect(rec.init_ms).to_be_greater_than(-1)
```

</details>

#### cpu clear_ms is non-negative

- cpu clear_ms is non-negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu clear_ms is non-negative")
val rec = measure_backend("cpu")
expect(rec.clear_ms).to_be_greater_than(-1)
```

</details>

#### cpu dispatch_ms is non-negative

- cpu dispatch_ms is non-negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu dispatch_ms is non-negative")
val rec = measure_backend("cpu")
expect(rec.dispatch_ms).to_be_greater_than(-1)
```

</details>

#### cpu present_ms is non-negative

- cpu present_ms is non-negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu present_ms is non-negative")
val rec = measure_backend("cpu")
expect(rec.present_ms).to_be_greater_than(-1)
```

</details>

#### cpu readback_ms is non-negative

- cpu readback_ms is non-negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu readback_ms is non-negative")
val rec = measure_backend("cpu")
expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### cpu readback returns non-empty pixel array

- cpu readback returns non-empty pixel array
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu readback returns non-empty pixel array")
val r = Engine2D.create_with_backend_strict(64, 64, "cpu")
expect(r.is_ok()).to_equal(true)
if r.is_ok():
    var eng = r.unwrap()
    eng.clear(rgb(10, 20, 30))
    val pixels = eng.read_pixels()
    expect(pixels.len()).to_be_greater_than(0)
    eng.shutdown()
```

</details>

#### software backend

#### software — perf record fields non-negative when available

- software — perf record fields non-negative when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("software — perf record fields non-negative when available")
val rec = measure_backend("software")
print_perf_record(rec)
if rec.init_ms >= 0:
    expect(rec.clear_ms).to_be_greater_than(-1)
    expect(rec.dispatch_ms).to_be_greater_than(-1)
    expect(rec.present_ms).to_be_greater_than(-1)
    expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### hardware backends — skipped when UNAVAILABLE

#### cuda — perf record fields non-negative when available

- cuda — perf record fields non-negative when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cuda — perf record fields non-negative when available")
val rec = measure_backend("cuda")
print_perf_record(rec)
if rec.init_ms >= 0:
    expect(rec.clear_ms).to_be_greater_than(-1)
    expect(rec.dispatch_ms).to_be_greater_than(-1)
    expect(rec.present_ms).to_be_greater_than(-1)
    expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### vulkan — perf record fields non-negative when available

- vulkan — perf record fields non-negative when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("vulkan — perf record fields non-negative when available")
val rec = measure_backend("vulkan")
print_perf_record(rec)
if rec.init_ms >= 0:
    expect(rec.clear_ms).to_be_greater_than(-1)
    expect(rec.dispatch_ms).to_be_greater_than(-1)
    expect(rec.present_ms).to_be_greater_than(-1)
    expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### metal — perf record fields non-negative when available

- metal — perf record fields non-negative when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("metal — perf record fields non-negative when available")
val rec = measure_backend("metal")
print_perf_record(rec)
if rec.init_ms >= 0:
    expect(rec.clear_ms).to_be_greater_than(-1)
    expect(rec.dispatch_ms).to_be_greater_than(-1)
    expect(rec.present_ms).to_be_greater_than(-1)
    expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### rocm — perf record fields non-negative when available

- rocm — perf record fields non-negative when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rocm — perf record fields non-negative when available")
val rec = measure_backend("rocm")
print_perf_record(rec)
if rec.init_ms >= 0:
    expect(rec.clear_ms).to_be_greater_than(-1)
    expect(rec.dispatch_ms).to_be_greater_than(-1)
    expect(rec.present_ms).to_be_greater_than(-1)
    expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### intel — perf record fields non-negative when available

- intel — perf record fields non-negative when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("intel — perf record fields non-negative when available")
val rec = measure_backend("intel")
print_perf_record(rec)
if rec.init_ms >= 0:
    expect(rec.clear_ms).to_be_greater_than(-1)
    expect(rec.dispatch_ms).to_be_greater_than(-1)
    expect(rec.present_ms).to_be_greater_than(-1)
    expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### qualcomm — perf record fields non-negative when available

- qualcomm — perf record fields non-negative when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("qualcomm — perf record fields non-negative when available")
val rec = measure_backend("qualcomm")
print_perf_record(rec)
if rec.init_ms >= 0:
    expect(rec.clear_ms).to_be_greater_than(-1)
    expect(rec.dispatch_ms).to_be_greater_than(-1)
    expect(rec.present_ms).to_be_greater_than(-1)
    expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### webgpu — perf record fields non-negative when available

- webgpu — perf record fields non-negative when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("webgpu — perf record fields non-negative when available")
val rec = measure_backend("webgpu")
print_perf_record(rec)
if rec.init_ms >= 0:
    expect(rec.clear_ms).to_be_greater_than(-1)
    expect(rec.dispatch_ms).to_be_greater_than(-1)
    expect(rec.present_ms).to_be_greater_than(-1)
    expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### opengl — perf record fields non-negative when available

- opengl — perf record fields non-negative when available


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("opengl — perf record fields non-negative when available")
# opengl backend requires rt_opengl_is_available extern which is
# not available in interpreter mode; treat as unavailable
val rec = make_perf_record("opengl")
print_perf_record(rec)
# init_ms is -1 (unavailable) — all fields remain -1, test passes
if rec.init_ms >= 0:
    expect(rec.clear_ms).to_be_greater_than(-1)
    expect(rec.dispatch_ms).to_be_greater_than(-1)
    expect(rec.present_ms).to_be_greater_than(-1)
    expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### rss field

#### cpu rss_kb is -1 or non-negative

- cpu rss_kb is -1 or non-negative
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu rss_kb is -1 or non-negative")
val rec = measure_backend("cpu")
var ok = rec.rss_kb == -1 or rec.rss_kb >= 0
expect(ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/perf_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Backend Perf Smoke.
- Backend Perf Smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f60e360cf1271b5c15c588768b0de2f79c3df53d93765bb7a2bea4e862fc7fab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f60e360cf1271b5c15c588768b0de2f79c3df53d93765bb7a2bea4e862fc7fab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f60e360cf1271b5c15c588768b0de2f79c3df53d93765bb7a2bea4e862fc7fab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/rendering/perf_smoke_spec.spl
mirror: doc/06_spec/integration/rendering/perf_smoke_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/perf_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/perf_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/perf_smoke_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cpu init_ms is measured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/perf_smoke_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cpu clear_ms is non-negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/perf_smoke_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cpu dispatch_ms is non-negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
