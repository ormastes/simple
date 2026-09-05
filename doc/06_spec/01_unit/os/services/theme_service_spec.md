# Theme Service Specification

> Tests covering ThemeService current_snapshot, ThemeService role_color, ThemeService singleton.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Theme Service Specification

## Scenarios

### ThemeService current_snapshot

#### returns a ThemeRenderSnapshot matching the active theme id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns a ThemeRenderSnapshot matching the active theme id
   - Expected: snapshot.id equals `service.active_theme_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a ThemeRenderSnapshot matching the active theme id")
val service = ThemeService.new()
val snapshot = service.current_snapshot()
expect(snapshot.id).to_equal(service.active_theme_name)
expect(snapshot.background_rgba).to_be_greater_than(0)
```

</details>

### ThemeService role_color

#### resolves a known role via the active theme's snapshot

- resolves a known role via the active theme's snapshot
   - Expected: resolved.role equals `document.text`
   - Expected: resolved.known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a known role via the active theme's snapshot")
val service = ThemeService.new()
val resolved = service.role_color("document.text")
expect(resolved.role).to_equal("document.text")
expect(resolved.known).to_equal(true)
expect(resolved.hex).to_start_with("#")
```

</details>

#### flags an unknown role instead of crashing

- flags an unknown role instead of crashing
   - Expected: resolved.known is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags an unknown role instead of crashing")
val service = ThemeService.new()
val resolved = service.role_color("not.a.real.role")
expect(resolved.known).to_equal(false)
```

</details>

### ThemeService singleton

#### get_theme_service returns a live instance with a snapshot

- get_theme_service returns a live instance with a snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_theme_service returns a live instance with a snapshot")
val service = get_theme_service()
val snapshot = service.current_snapshot()
expect(snapshot.id.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/theme_service_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ThemeService current_snapshot, ThemeService role_color, ThemeService singleton.
- ThemeService current_snapshot
- ThemeService role_color
- ThemeService singleton

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `79006fd53c9f3d6c472b0f2b3f2635aded9b5ccfdc5d1ad766bfba2a22e4a04c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79006fd53c9f3d6c472b0f2b3f2635aded9b5ccfdc5d1ad766bfba2a22e4a04c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79006fd53c9f3d6c472b0f2b3f2635aded9b5ccfdc5d1ad766bfba2a22e4a04c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/services/theme_service_spec.spl
mirror: doc/06_spec/01_unit/os/services/theme_service_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/theme_service_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/theme_service_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/theme_service_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a ThemeRenderSnapshot matching the active theme id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/theme_service_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a known role via the active theme's snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/theme_service_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags an unknown role instead of crashing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
