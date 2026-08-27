# Occlusion Specification

> Tests covering Occlusion — no hits, Occlusion — one hit, Occlusion — two hits, Occlusion — disabled.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Occlusion Specification

## Scenarios

### Occlusion — no hits

#### zero hits returns 1.0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- zero hits returns 1.0
   - Expected: mult > 0.99 is true
   - Expected: mult < 1.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zero hits returns 1.0")
val config = default_occlusion_config()
val listener = Vec2(x: 0.0, y: 0.0)
val source = Vec2(x: 10.0, y: 0.0)
val mult = compute_occlusion_2d(listener, source, 0, config)
expect(mult > 0.99).to_equal(true)
expect(mult < 1.01).to_equal(true)
```

</details>

### Occlusion — one hit

#### one hit with attenuation 0.5 returns 0.5

- one hit with attenuation 0.5 returns 0.5
   - Expected: mult > 0.49 is true
   - Expected: mult < 0.51 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("one hit with attenuation 0.5 returns 0.5")
val config = default_occlusion_config()
val listener = Vec2(x: 0.0, y: 0.0)
val source = Vec2(x: 10.0, y: 0.0)
val mult = compute_occlusion_2d(listener, source, 1, config)
expect(mult > 0.49).to_equal(true)
expect(mult < 0.51).to_equal(true)
```

</details>

### Occlusion — two hits

#### two hits with attenuation 0.5 returns 0.25

- two hits with attenuation 0.5 returns 0.25
   - Expected: mult > 0.24 is true
   - Expected: mult < 0.26 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("two hits with attenuation 0.5 returns 0.25")
val config = default_occlusion_config()
val listener = Vec2(x: 0.0, y: 0.0)
val source = Vec2(x: 10.0, y: 0.0)
val mult = compute_occlusion_2d(listener, source, 2, config)
expect(mult > 0.24).to_equal(true)
expect(mult < 0.26).to_equal(true)
```

</details>

### Occlusion — disabled

#### disabled occlusion returns 1.0

- disabled occlusion returns 1.0
   - Expected: mult > 0.99 is true
   - Expected: mult < 1.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disabled occlusion returns 1.0")
val config = OcclusionConfig(enabled: false, max_ray_distance: 1000.0, attenuation_per_hit: 0.5)
val listener = Vec2(x: 0.0, y: 0.0)
val source = Vec2(x: 10.0, y: 0.0)
val mult = compute_occlusion_2d(listener, source, 3, config)
expect(mult > 0.99).to_equal(true)
expect(mult < 1.01).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/occlusion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Occlusion — no hits, Occlusion — one hit, Occlusion — two hits, Occlusion — disabled.
- Occlusion — no hits
- Occlusion — one hit
- Occlusion — two hits
- Occlusion — disabled

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c2a07fd4dd38e1675d00116bd24fe67f933540537e1314b7a6688e12469628e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2a07fd4dd38e1675d00116bd24fe67f933540537e1314b7a6688e12469628e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2a07fd4dd38e1675d00116bd24fe67f933540537e1314b7a6688e12469628e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/occlusion_spec.spl
mirror: doc/06_spec/03_system/gui/occlusion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/occlusion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/occlusion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/occlusion_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero hits returns 1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/occlusion_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'one hit with attenuation 0.5 returns 0.5' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/occlusion_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two hits with attenuation 0.5 returns 0.25' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
