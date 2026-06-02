# Engine2d Backend Specification

## Scenarios

### Engine2D Backend Lifecycle Smoke

#### quick lifecycle backend list

#### returns at least software and cpu

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backends = quick_lifecycle_backends()
var has_software = false
var has_cpu_simd = false
var has_cpu = false
for b in backends:
    if b == "software":
        has_software = true
    if b == "cpu_simd":
        has_cpu_simd = true
    if b == "cpu":
        has_cpu = true
expect(has_software).to_equal(true)
expect(has_cpu_simd).to_equal(true)
expect(has_cpu).to_equal(true)
```

</details>

#### returns a non-empty list

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backends = quick_lifecycle_backends()
expect(backends.len()).to_be_greater_than(1)
```

</details>

#### software backend

#### initializes with correct dimensions

1. var backend = SoftwareBackend create
   - Expected: backend.init(100, 100) is true
   - Expected: backend.name() equals `software`
   - Expected: backend.width() equals `100`
   - Expected: backend.height() equals `100`

2. backend shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareBackend.create()
expect(backend.init(100, 100)).to_equal(true)
expect(backend.name()).to_equal("software")
expect(backend.width()).to_equal(100)
expect(backend.height()).to_equal(100)
backend.shutdown()
```

</details>

#### read_pixels works after initialization

1. var backend = SoftwareBackend create
   - Expected: backend.init(10, 10) is true
   - Expected: pixels.len() equals `100`

2. backend shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareBackend.create()
expect(backend.init(10, 10)).to_equal(true)
val pixels = backend.read_pixels()
expect(pixels.len()).to_equal(100)
backend.shutdown()
```

</details>

#### shutdown releases dimensions and pixels

1. var backend = SoftwareBackend create
   - Expected: backend.init(16, 16) is true

2. backend clear

3. backend present
   - Expected: backend.read_pixels().len() equals `256`

4. backend shutdown
   - Expected: backend.width() equals `0`
   - Expected: backend.height() equals `0`
   - Expected: backend.read_pixels().len() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareBackend.create()
expect(backend.init(16, 16)).to_equal(true)
backend.clear(rgb(0, 0, 0))
backend.present()
expect(backend.read_pixels().len()).to_equal(256)
backend.shutdown()
expect(backend.width()).to_equal(0)
expect(backend.height()).to_equal(0)
expect(backend.read_pixels().len()).to_equal(0)
```

</details>

#### cpu backend

#### initializes through the software raster surface

1. var backend = CpuBackend create
   - Expected: backend.init(100, 100) is true
   - Expected: backend.name() equals `cpu`
   - Expected: backend.width() equals `100`
   - Expected: backend.height() equals `100`

2. backend shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = CpuBackend.create()
expect(backend.init(100, 100)).to_equal(true)
expect(backend.name()).to_equal("cpu")
expect(backend.width()).to_equal(100)
expect(backend.height()).to_equal(100)
backend.shutdown()
```

</details>

#### draws and reads pixels

1. var backend = CpuBackend create
   - Expected: backend.init(12, 12) is true

2. backend clear

3. backend draw rect filled

4. backend present
   - Expected: pixels.len() equals `144`
   - Expected: pixels[2 * 12 + 2] equals `rgb(10, 20, 30)`

5. backend shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = CpuBackend.create()
expect(backend.init(12, 12)).to_equal(true)
backend.clear(rgb(1, 2, 3))
backend.draw_rect_filled(2, 2, 4, 4, rgb(10, 20, 30))
backend.present()
val pixels = backend.read_pixels()
expect(pixels.len()).to_equal(144)
expect(pixels[2 * 12 + 2]).to_equal(rgb(10, 20, 30))
backend.shutdown()
```

</details>

#### can create multiple backends sequentially

1. var e1 = SoftwareBackend create
   - Expected: e1.init(64, 64) is true

2. e1 shutdown

3. var e2 = CpuBackend create
   - Expected: e2.init(128, 128) is true

4. e2 shutdown

5. var e3 = SoftwareBackend create
   - Expected: e3.init(32, 32) is true
   - Expected: e3.width() equals `32`

6. e3 shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e1 = SoftwareBackend.create()
expect(e1.init(64, 64)).to_equal(true)
e1.shutdown()
var e2 = CpuBackend.create()
expect(e2.init(128, 128)).to_equal(true)
e2.shutdown()
var e3 = SoftwareBackend.create()
expect(e3.init(32, 32)).to_equal(true)
expect(e3.width()).to_equal(32)
e3.shutdown()
```

</details>

#### Engine2D explicit backend selection

#### cpu_simd is a first-class strict backend alias

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = Engine2D.probe_backend(16, 16, "cpu_simd")
expect(probe.status).to_equal(BackendStatus.Initialized)
expect(probe.selected_name).to_equal("cpu_simd")
```

</details>

#### simd_cpu alias renders through the CPU SIMD surface

1. reset simd hits

2. var engine = Engine2D create with backend

3. engine clear

4. engine draw rect filled

5. engine present
   - Expected: engine.backend_name() equals `cpu_simd`
   - Expected: pixels.len() equals `256`
   - Expected: pixels[2 * 16 + 2] equals `rgb(10, 20, 30)`

6. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_simd_hits()
var engine = Engine2D.create_with_backend(16, 16, "simd_cpu")
engine.clear(rgb(1, 2, 3))
engine.draw_rect_filled(2, 2, 4, 4, rgb(10, 20, 30))
engine.present()
val pixels = engine.read_pixels()
val hits = simd_hit_counts()
expect(engine.backend_name()).to_equal("cpu_simd")
expect(pixels.len()).to_equal(256)
expect(pixels[2 * 16 + 2]).to_equal(rgb(10, 20, 30))
expect(hits.fill_hits).to_be_greater_than(0)
engine.shutdown()
```

</details>

#### metal strict probe does not silently fall back to cpu

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = Engine2D.probe_backend(16, 16, "metal")
if is_macos():
    expect(probe.selected_name).to_equal("metal")
else:
    expect(probe.status).to_equal(BackendStatus.Unavailable)
    expect(probe.selected_name).to_equal("metal")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/engine2d_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D Backend Lifecycle Smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

