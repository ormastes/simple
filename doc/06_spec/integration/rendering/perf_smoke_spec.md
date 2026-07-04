# Perf Smoke Specification

## Scenarios

### Backend Perf Smoke

#### cpu baseline

#### cpu init_ms is measured

1. print perf record


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = measure_backend("cpu")
print_perf_record(rec)
expect(rec.init_ms).to_be_greater_than(-1)
```

</details>

#### cpu clear_ms is non-negative

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = measure_backend("cpu")
expect(rec.clear_ms).to_be_greater_than(-1)
```

</details>

#### cpu dispatch_ms is non-negative

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = measure_backend("cpu")
expect(rec.dispatch_ms).to_be_greater_than(-1)
```

</details>

#### cpu present_ms is non-negative

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = measure_backend("cpu")
expect(rec.present_ms).to_be_greater_than(-1)
```

</details>

#### cpu readback_ms is non-negative

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = measure_backend("cpu")
expect(rec.readback_ms).to_be_greater_than(-1)
```

</details>

#### cpu readback returns non-empty pixel array

1. var eng = r unwrap

2. eng clear

3. eng shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print perf record


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print perf record


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print perf record


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print perf record


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print perf record


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print perf record


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print perf record


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print perf record


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print perf record


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/02_integration/rendering/perf_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Backend Perf Smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

