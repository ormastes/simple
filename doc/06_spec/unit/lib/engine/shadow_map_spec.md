# Shadow Map Specification

> Tests covering ShadowMapConfig, CascadedShadowMap, ShadowSystem.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shadow Map Specification

## Scenarios

### ShadowMapConfig

#### creates default config

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates default config
   - Expected: cfg.resolution equals `1024`
   - Expected: cfg.bias equals `0.005`
   - Expected: cfg.normal_bias equals `0.02`
   - Expected: cfg.soft_shadows is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default config")
val cfg = ShadowMapConfig.default_config()
expect(cfg.resolution).to_equal(1024)
expect(cfg.bias).to_equal(0.005)
expect(cfg.normal_bias).to_equal(0.02)
expect(cfg.soft_shadows).to_equal(true)
```

</details>

#### creates high quality config

- creates high quality config
   - Expected: cfg.resolution equals `2048`
   - Expected: cfg.bias equals `0.003`
   - Expected: cfg.normal_bias equals `0.01`
   - Expected: cfg.soft_shadows is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates high quality config")
val cfg = ShadowMapConfig.high_quality()
expect(cfg.resolution).to_equal(2048)
expect(cfg.bias).to_equal(0.003)
expect(cfg.normal_bias).to_equal(0.01)
expect(cfg.soft_shadows).to_equal(true)
```

</details>

### CascadedShadowMap

#### creates with correct cascade count

- creates with correct cascade count
   - Expected: csm.cascade_count equals `4`
   - Expected: csm.cascades.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with correct cascade count")
val cfg = ShadowMapConfig.default_config()
val csm = CascadedShadowMap.new(4, cfg)
expect(csm.cascade_count).to_equal(4)
expect(csm.cascades.len()).to_equal(4)
```

</details>

#### generates increasing split distances

- generates increasing split distances
   - Expected: c0.split_distance < c1.split_distance is true
   - Expected: c1.split_distance < c2.split_distance is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates increasing split distances")
val cfg = ShadowMapConfig.default_config()
val csm = CascadedShadowMap.new(3, cfg)
val c0 = csm.cascades[0]
val c1 = csm.cascades[1]
val c2 = csm.cascades[2]
expect(c0.split_distance < c1.split_distance).to_equal(true)
expect(c1.split_distance < c2.split_distance).to_equal(true)
```

</details>

#### gets cascade by valid index

- gets cascade by valid index
   - Expected: level.split_distance > 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets cascade by valid index")
val cfg = ShadowMapConfig.default_config()
val csm = CascadedShadowMap.new(2, cfg)
val maybe = csm.get_cascade(0)
if val Some(level) = maybe:
    expect(level.split_distance > 0.0).to_equal(true)
```

</details>

#### returns None for invalid cascade index

- returns None for invalid cascade index
   - Expected: 1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for invalid cascade index")
val cfg = ShadowMapConfig.default_config()
val csm = CascadedShadowMap.new(2, cfg)
val maybe = csm.get_cascade(5)
if val Some(level) = maybe:
    expect(1).to_equal(0)
```

</details>

#### computes total resolution

- computes total resolution
   - Expected: total equals `1536`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes total resolution")
val cfg = ShadowMapConfig.default_config()
val csm = CascadedShadowMap.new(2, cfg)
val total = csm.total_resolution()
# First cascade: 1024, second: 512
expect(total).to_equal(1536)
```

</details>

### ShadowSystem

#### starts enabled

- starts enabled
   - Expected: sys.is_enabled() is true
   - Expected: sys.shadow_map_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts enabled")
val cfg = ShadowMapConfig.default_config()
val sys = ShadowSystem.new(cfg)
expect(sys.is_enabled()).to_equal(true)
expect(sys.shadow_map_count()).to_equal(0)
```

</details>

#### adds shadow maps

- adds shadow maps
   - Expected: idx equals `0`
   - Expected: sys.shadow_map_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds shadow maps")
val cfg = ShadowMapConfig.default_config()
var sys = ShadowSystem.new(cfg)
val csm = CascadedShadowMap.new(3, cfg)
val idx = sys.add_shadow_map(csm)
expect(idx).to_equal(0)
expect(sys.shadow_map_count()).to_equal(1)
```

</details>

#### toggles enabled state

- toggles enabled state
   - Expected: sys.is_enabled() is false
   - Expected: sys.is_enabled() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("toggles enabled state")
val cfg = ShadowMapConfig.default_config()
var sys = ShadowSystem.new(cfg)
sys.set_enabled(false)
expect(sys.is_enabled()).to_equal(false)
sys.set_enabled(true)
expect(sys.is_enabled()).to_equal(true)
```

</details>

#### clears all shadow maps

- clears all shadow maps
   - Expected: sys.shadow_map_count() equals `2`
   - Expected: sys.shadow_map_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all shadow maps")
val cfg = ShadowMapConfig.default_config()
var sys = ShadowSystem.new(cfg)
sys.add_shadow_map(CascadedShadowMap.new(2, cfg))
sys.add_shadow_map(CascadedShadowMap.new(4, cfg))
expect(sys.shadow_map_count()).to_equal(2)
sys.clear()
expect(sys.shadow_map_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/engine/shadow_map_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ShadowMapConfig, CascadedShadowMap, ShadowSystem.
- ShadowMapConfig
- CascadedShadowMap
- ShadowSystem

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `5fd383c35d34298de5cec42fb86365c79dbf67b6e0d8c69691e38e8471e6b2d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fd383c35d34298de5cec42fb86365c79dbf67b6e0d8c69691e38e8471e6b2d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fd383c35d34298de5cec42fb86365c79dbf67b6e0d8c69691e38e8471e6b2d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/engine/shadow_map_spec.spl
mirror: doc/06_spec/unit/lib/engine/shadow_map_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/engine/shadow_map_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/engine/shadow_map_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/engine/shadow_map_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/engine/shadow_map_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates default config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/shadow_map_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates high quality config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/shadow_map_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with correct cascade count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
