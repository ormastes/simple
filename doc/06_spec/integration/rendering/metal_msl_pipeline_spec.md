# Metal Msl Pipeline Specification

## Scenarios

### Metal MSL compile + GPU dispatch

#### on macOS

#### MSL compiles: all compute pipelines created

1. var b = MetalBackend create
   - Expected: ok is true

2. b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var b = MetalBackend.create()
    val ok = b.init(16, 16)
    expect(ok).to_equal(true)
    expect(b.session.pipe_clear).to_be_greater_than(0)
    expect(b.session.pipe_rect_filled).to_be_greater_than(0)
    expect(b.session.pipe_line).to_be_greater_than(0)
    expect(b.session.pipe_circle).to_be_greater_than(0)
    expect(b.session.pipe_triangle).to_be_greater_than(0)
    expect(b.session.pipe_gradient).to_be_greater_than(0)
    expect(b.session.pipe_blit).to_be_greater_than(0)
    b.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### GPU clear dispatch runs (1d) and marks dirty

1. var b = MetalBackend create

2. b init

3. b clear
   - Expected: b.dirty is true

4. b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var b = MetalBackend.create()
    b.init(16, 16)
    b.clear(rgb(3, 5, 7))
    expect(b.dirty).to_equal(true)
    b.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### GPU rect_filled dispatch runs (2d) and marks dirty

1. var b = MetalBackend create

2. b init

3. b draw rect filled
   - Expected: b.dirty is true

4. b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var b = MetalBackend.create()
    b.init(16, 16)
    b.draw_rect_filled(0, 0, 8, 8, rgb(40, 70, 100))
    expect(b.dirty).to_equal(true)
    b.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/metal_msl_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Metal MSL compile + GPU dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

