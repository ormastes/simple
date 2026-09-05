# Game2d Config Facade Specification

> Tests covering gc_async_mut game2d config facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Config Facade Specification

## Scenarios

### gc_async_mut game2d config facade

#### re-exports game configuration defaults

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports game configuration defaults
   - Expected: window.width equals `800`
   - Expected: window.height equals `600`
   - Expected: window.vsync is true
   - Expected: runtime.fixed_step_hz equals `60`
   - Expected: runtime.max_entities equals `1024`
   - Expected: config.title equals `Simple Game`
   - Expected: config.startup_scene equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports game configuration defaults")
val window = WindowConfig.default()
expect(window.width).to_equal(800)
expect(window.height).to_equal(600)
expect(window.vsync).to_equal(true)

val runtime = RuntimeConfig.default()
expect(runtime.fixed_step_hz).to_equal(60)
expect(runtime.max_entities).to_equal(1024)

val config = GameConfig.default()
expect(config.title).to_equal("Simple Game")
expect(config.startup_scene).to_equal("main")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/game2d/config/game2d_config_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut game2d config facade.
- gc_async_mut game2d config facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `9da44bf7db3b11a69b2f21ddf749c201ecb0202c3342f1718ce1b1faf9f7faff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9da44bf7db3b11a69b2f21ddf749c201ecb0202c3342f1718ce1b1faf9f7faff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9da44bf7db3b11a69b2f21ddf749c201ecb0202c3342f1718ce1b1faf9f7faff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/gc_async_mut/game2d/config/game2d_config_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/game2d/config/game2d_config_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/game2d/config/game2d_config_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/game2d/config/game2d_config_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/game2d/config/game2d_config_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/game2d/config/game2d_config_facade_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports game configuration defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
