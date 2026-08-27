# engine2d_backend_spec

> Purpose: This spec proves Engine2D Backend Lifecycle Smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# engine2d_backend_spec

Purpose: This spec proves Engine2D Backend Lifecycle Smoke.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Engine2D Backend Lifecycle Smoke.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Engine2D Backend Lifecycle Smoke

#### quick lifecycle backend list

#### returns at least software and cpu

- returns at least software and cpu
   - Expected: has_software is true
   - Expected: has_cpu_simd is true
   - Expected: has_cpu is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-ENGINE2DBACKEND-001
step("returns at least software and cpu")
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

- returns a non-empty list
- returns a non-empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a non-empty list")
step("returns a non-empty list")
val backends = quick_lifecycle_backends()
expect(backends.len()).to_be_greater_than(1)
```

</details>

#### software backend

#### initializes with correct dimensions

- initializes with correct dimensions
- initializes with correct dimensions
   - Expected: backend.init(100, 100) is true
   - Expected: backend.name() equals `software`
   - Expected: backend.width() equals `100`
   - Expected: backend.height() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("initializes with correct dimensions")
step("initializes with correct dimensions")
var backend = SoftwareBackend.create()
expect(backend.init(100, 100)).to_equal(true)
expect(backend.name()).to_equal("software")
expect(backend.width()).to_equal(100)
expect(backend.height()).to_equal(100)
backend.shutdown()
```

</details>

#### read_pixels works after initialization

- read_pixels works after initialization
- read_pixels works after initialization
   - Expected: backend.init(10, 10) is true
   - Expected: pixels.len() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read_pixels works after initialization")
step("read_pixels works after initialization")
var backend = SoftwareBackend.create()
expect(backend.init(10, 10)).to_equal(true)
val pixels = backend.read_pixels()
expect(pixels.len()).to_equal(100)
backend.shutdown()
```

</details>

#### shutdown releases dimensions and pixels

- shutdown releases dimensions and pixels
- shutdown releases dimensions and pixels
   - Expected: backend.init(16, 16) is true
   - Expected: backend.read_pixels().len() equals `256`
   - Expected: backend.width() equals `0`
   - Expected: backend.height() equals `0`
   - Expected: backend.read_pixels().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shutdown releases dimensions and pixels")
step("shutdown releases dimensions and pixels")
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

- initializes through the software raster surface
- initializes through the software raster surface
   - Expected: backend.init(100, 100) is true
   - Expected: backend.name() equals `cpu`
   - Expected: backend.width() equals `100`
   - Expected: backend.height() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("initializes through the software raster surface")
step("initializes through the software raster surface")
var backend = CpuBackend.create()
expect(backend.init(100, 100)).to_equal(true)
expect(backend.name()).to_equal("cpu")
expect(backend.width()).to_equal(100)
expect(backend.height()).to_equal(100)
backend.shutdown()
```

</details>

#### draws and reads pixels

- draws and reads pixels
- draws and reads pixels
   - Expected: backend.init(12, 12) is true
   - Expected: pixels.len() equals `144`
   - Expected: pixels[2 * 12 + 2] equals `rgb(10, 20, 30)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draws and reads pixels")
step("draws and reads pixels")
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

- can create multiple backends sequentially
- can create multiple backends sequentially
   - Expected: e1.init(64, 64) is true
   - Expected: e2.init(128, 128) is true
   - Expected: e3.init(32, 32) is true
   - Expected: e3.width() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can create multiple backends sequentially")
step("can create multiple backends sequentially")
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

#### documents the default backend preference as Metal then CUDA HIP then Vulkan

- documents the default backend preference as Metal then CUDA HIP then Vulkan
- documents the default backend preference as Metal then CUDA HIP then Vul
   - Expected: order[0] equals `metal`
   - Expected: order[1] equals `cuda`
   - Expected: order[2] equals `rocm`
   - Expected: order[4] equals `vulkan`
   - Expected: order[5] equals `directx`
   - Expected: order[6] equals `opencl`
   - Expected: order[order.len() - 1] equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("documents the default backend preference as Metal then CUDA HIP then Vulkan")
step("documents the default backend preference as Metal then CUDA HIP then Vul")
val order = backend_default_priority_order()
expect(order[0]).to_equal("metal")
expect(order[1]).to_equal("cuda")
expect(order[2]).to_equal("rocm")
expect(order[4]).to_equal("vulkan")
expect(order[5]).to_equal("directx")
expect(order[6]).to_equal("opencl")
expect(order[order.len() - 1]).to_equal("cpu")
expect(backend_preference_summary()).to_contain("metal > cuda > rocm/hip")
expect(backend_preference_summary()).to_contain("vulkan > directx > opencl")
```

</details>

#### canonicalizes HIP and SIMD aliases before backend selection

- canonicalizes HIP and SIMD aliases before backend selection
- canonicalizes HIP and SIMD aliases before backend selection
   - Expected: backend_canonical_name("hip") equals `rocm`
   - Expected: backend_canonical_name("AMD-HIP") equals `rocm`
   - Expected: backend_canonical_name("simd-cpu") equals `cpu_simd`
   - Expected: backend_priority("hip") equals `backend_priority("rocm")`
   - Expected: backend_is_hardware("hip") is true
   - Expected: backend_requires_gpu("hip") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("canonicalizes HIP and SIMD aliases before backend selection")
step("canonicalizes HIP and SIMD aliases before backend selection")
expect(backend_canonical_name("hip")).to_equal("rocm")
expect(backend_canonical_name("AMD-HIP")).to_equal("rocm")
expect(backend_canonical_name("simd-cpu")).to_equal("cpu_simd")
expect(backend_priority("hip")).to_equal(backend_priority("rocm"))
expect(backend_is_hardware("hip")).to_equal(true)
expect(backend_requires_gpu("hip")).to_equal(true)
expect(feature_gate_description("hip")).to_contain("ROCm")
```

</details>

#### cpu_simd is a first-class strict backend alias

- cpu_simd is a first-class strict backend alias
- cpu_simd is a first-class strict backend alias
   - Expected: probe.status equals `BackendStatus.Initialized`
   - Expected: probe.selected_name equals `cpu_simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu_simd is a first-class strict backend alias")
step("cpu_simd is a first-class strict backend alias")
val probe = Engine2D.probe_backend(16, 16, "cpu_simd")
expect(probe.status).to_equal(BackendStatus.Initialized)
expect(probe.selected_name).to_equal("cpu_simd")
expect(probe.reason).to_contain("Native CPU SIMD pixel rows available")
```

</details>

#### hip alias probes the ROCm HIP backend instead of unknown fallback

- hip alias probes the ROCm HIP backend instead of unknown fallback
- hip alias probes the ROCm HIP backend instead of unknown fallback
   - Expected: probe.selected_name equals `rocm`
   - Expected: probe.backend_name equals `rocm`
   - Expected: probe.status == BackendStatus.Initialized or probe.status == BackendStatus.Unavailable or probe.status == BackendStatus.Failed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("hip alias probes the ROCm HIP backend instead of unknown fallback")
step("hip alias probes the ROCm HIP backend instead of unknown fallback")
val probe = Engine2D.probe_backend(16, 16, "hip")
expect(probe.selected_name).to_equal("rocm")
expect(probe.backend_name).to_equal("rocm")
expect(probe.status == BackendStatus.Initialized or probe.status == BackendStatus.Unavailable or probe.status == BackendStatus.Failed).to_equal(true)
expect(probe.reason).to_contain("ROCm")
```

</details>

#### simd_cpu alias renders through the CPU SIMD surface

- simd_cpu alias renders through the CPU SIMD surface
- simd_cpu alias renders through the CPU SIMD surface
   - Expected: engine.backend_name() equals `cpu_simd`
   - Expected: pixels.len() equals `256`
   - Expected: pixels[2 * 16 + 2] equals `rgb(10, 20, 30)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd_cpu alias renders through the CPU SIMD surface")
step("simd_cpu alias renders through the CPU SIMD surface")
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

- metal strict probe does not silently fall back to cpu
- metal strict probe does not silently fall back to cpu
   - Expected: probe.selected_name equals `metal`
   - Expected: probe.status equals `BackendStatus.Unavailable`
   - Expected: probe.selected_name equals `metal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("metal strict probe does not silently fall back to cpu")
step("metal strict probe does not silently fall back to cpu")
val probe = Engine2D.probe_backend(16, 16, "metal")
if is_macos():
    expect(probe.selected_name).to_equal("metal")
else:
    expect(probe.status).to_equal(BackendStatus.Unavailable)
    expect(probe.selected_name).to_equal("metal")
```

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-ENGINE2DBACKEND-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fa78311d0e0348f1088bad1f6f2a6ad7fe59efb8cd6c885dd15c977711bd2a61`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa78311d0e0348f1088bad1f6f2a6ad7fe59efb8cd6c885dd15c977711bd2a61`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa78311d0e0348f1088bad1f6f2a6ad7fe59efb8cd6c885dd15c977711bd2a61`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/02_integration/rendering/engine2d_backend_spec.spl
mirror: doc/06_spec/02_integration/rendering/engine2d_backend_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/engine2d_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/engine2d_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/engine2d_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/engine2d_backend_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns at least software and cpu' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/engine2d_backend_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a non-empty list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/engine2d_backend_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes with correct dimensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/engine2d_backend_spec.spl:131:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can create multiple backends sequentially' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
