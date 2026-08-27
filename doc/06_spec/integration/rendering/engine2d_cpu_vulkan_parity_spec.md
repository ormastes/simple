# Engine2d Cpu Vulkan Parity Specification

> Tests covering Engine2D CPU and Vulkan rendering parity baseline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Cpu Vulkan Parity Specification

## Scenarios

### Engine2D CPU and Vulkan rendering parity baseline

#### core primitives

#### keeps cpu rendering deterministic

- keeps cpu rendering deterministic
   - Expected: parity_pixels_equal(first, second) is true
   - Expected: parity_pixel_at(first, 2, 2, 32) equals `rgb(40, 70, 100)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps cpu rendering deterministic")
val first = render_cpu_vulkan_core_scene("cpu")
val second = render_cpu_vulkan_core_scene("cpu")
expect(parity_pixels_equal(first, second)).to_equal(true)
expect(parity_pixel_at(first, 2, 2, 32)).to_equal(rgb(40, 70, 100))
```

</details>

#### matches the software reference for core primitives

- matches the software reference for core primitives
   - Expected: parity_pixels_equal(software, cpu) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the software reference for core primitives")
val software = render_cpu_vulkan_core_scene("software")
val cpu = render_cpu_vulkan_core_scene("cpu")
expect(parity_pixels_equal(software, cpu)).to_equal(true)
```

</details>

#### vulkan availability path

#### creates the Vulkan backend object without resolving the nogc session constructor

- creates the Vulkan backend object without resolving the nogc session constructor
   - Expected: backend.name() equals `vulkan`
   - Expected: backend.width() equals `0`
   - Expected: backend.height() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates the Vulkan backend object without resolving the nogc session constructor")
var backend = VulkanBackend.create()
expect(backend.name()).to_equal("vulkan")
expect(backend.width()).to_equal(0)
expect(backend.height()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D CPU and Vulkan rendering parity baseline.
- Engine2D CPU and Vulkan rendering parity baseline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `5825af20176e0755506b98812a529d40533ebebeb12a528f74c8ff7063543863`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5825af20176e0755506b98812a529d40533ebebeb12a528f74c8ff7063543863`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5825af20176e0755506b98812a529d40533ebebeb12a528f74c8ff7063543863`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl
mirror: doc/06_spec/integration/rendering/engine2d_cpu_vulkan_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/engine2d_cpu_vulkan_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/engine2d_cpu_vulkan_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps cpu rendering deterministic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the software reference for core primitives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates the Vulkan backend object without resolving the nogc session constructor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
