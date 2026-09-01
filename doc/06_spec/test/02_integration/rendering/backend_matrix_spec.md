# Backend Matrix Specification

> <details>

<!-- sdn-diagram:id=backend_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_matrix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Matrix Specification

## Scenarios

### Backend Matrix — Forced-Backend Probe

#### hardware backends

#### cuda probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- print probe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_one("cuda")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### vulkan probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- print probe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_one("vulkan")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### metal probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- print probe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_one("metal")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### rocm probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- print probe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_one("rocm")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### intel probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- print probe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_one("intel")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### qualcomm probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- print probe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_one("qualcomm")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### webgpu probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- print probe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_one("webgpu")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### opengl probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- print probe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_one("opengl")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### software backends

#### software probe — SOFTWARE_PASS or FAILED

- print probe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_one("software")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "SOFTWARE_PASS" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### baseline cpu backend

#### cpu probe always passes

- print probe
   - Expected: label equals `SOFTWARE_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_one("cpu")
val label = probe_result_label(probe)
print_probe(probe)
expect(label).to_equal("SOFTWARE_PASS")
```

</details>

#### cpu strict result is not Err

- var eng = r unwrap
- eng shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Engine2D.create_with_backend_strict(16, 16, "cpu")
expect(r.is_ok()).to_equal(true)
if r.is_ok():
    var eng = r.unwrap()
    eng.shutdown()
```

</details>

#### no silent fallback

#### strict cuda never returns cpu on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Engine2D.create_with_backend_strict(16, 16, "cuda")
if not r.is_ok():
    val probe = r.unwrap_err()
    val is_fallback = probe.is_ok() and probe.selected_name == "cpu"
    expect(is_fallback).to_equal(false)
```

</details>

#### strict vulkan never returns cpu on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if not r.is_ok():
    val probe = r.unwrap_err()
    val is_fallback = probe.is_ok() and probe.selected_name == "cpu"
    expect(is_fallback).to_equal(false)
```

</details>

#### strict metal never returns cpu on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Engine2D.create_with_backend_strict(16, 16, "metal")
if not r.is_ok():
    val probe = r.unwrap_err()
    val is_fallback = probe.is_ok() and probe.selected_name == "cpu"
    expect(is_fallback).to_equal(false)
```

</details>

#### strict webgpu never returns cpu on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Engine2D.create_with_backend_strict(16, 16, "webgpu")
if not r.is_ok():
    val probe = r.unwrap_err()
    val is_fallback = probe.is_ok() and probe.selected_name == "cpu"
    expect(is_fallback).to_equal(false)
```

</details>

#### unknown backend returns Err not cpu

- print probe
   - Expected: probe.requested_name equals `does-not-exist`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Engine2D.create_with_backend_strict(16, 16, "does-not-exist")
expect(r.is_ok()).to_equal(false)
val probe = r.unwrap_err()
print_probe(probe)
expect(probe.requested_name).to_equal("does-not-exist")
```

</details>

#### diagnostics

#### failed probe includes requested_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Engine2D.create_with_backend_strict(16, 16, "cuda")
if not r.is_ok():
    val probe = r.unwrap_err()
    expect(probe.requested_name).to_equal("cuda")
```

</details>

#### failed probe includes fallback_reason when unavailable

- var reason present = probe fallback reason len
   - Expected: reason_present is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Engine2D.create_with_backend_strict(16, 16, "metal")
if not r.is_ok():
    val probe = r.unwrap_err()
    if probe.status == BackendStatus.Unavailable:
        var reason_present = probe.fallback_reason.len() > 0
        expect(reason_present).to_equal(true)
```

</details>

#### diagnostic_text contains requested and selected fields

- var has requested = diag contains
- var has selected = diag contains
   - Expected: has_requested is true
   - Expected: has_selected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Engine2D.create_with_backend_strict(16, 16, "cuda")
if not r.is_ok():
    val probe = r.unwrap_err()
    val diag = probe.diagnostic_text()
    var has_requested = diag.contains("requested=cuda")
    var has_selected = diag.contains("selected=")
    expect(has_requested).to_equal(true)
    expect(has_selected).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/backend_matrix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Backend Matrix — Forced-Backend Probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
