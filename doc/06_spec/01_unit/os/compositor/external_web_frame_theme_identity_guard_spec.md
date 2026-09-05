# External Web Frame Theme Identity Guard Specification

> Tests covering external Web frame acceptance is theme-identity gated, detection: the guard must not be bypassable, and must not over-reject.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# External Web Frame Theme Identity Guard Specification

## Scenarios

### external Web frame acceptance is theme-identity gated

#### refuses a frame carrying a theme id that is not the active theme

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- refuses a frame carrying a theme id that is not the active theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a frame carrying a theme id that is not the active theme")
val body = "<div>first parent body</div>"
var comp = _registered_compositor(body)
expect(comp.require_external_web_frame(1)).to_be(true)
val revision = simple_web_content_revision_with_theme(
    default_theme_id(), "First", body, 104, 80, 0
)
val hostile = _frame("1", revision, "attacker-theme-never-installed")
expect(comp.set_external_web_frame(1, hostile)).to_be(false)
```

</details>

#### refuses a frame carrying no theme id at all

- refuses a frame carrying no theme id at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a frame carrying no theme id at all")
val body = "<div>first parent body</div>"
var comp = _registered_compositor(body)
expect(comp.require_external_web_frame(1)).to_be(true)
val revision = simple_web_content_revision_with_theme(
    default_theme_id(), "First", body, 104, 80, 0
)
expect(comp.set_external_web_frame(1, _frame("1", revision, ""))).to_be(false)
```

</details>

### detection: the guard must not be bypassable, and must not over-reject

#### still accepts a frame whose theme id IS the active theme

- still accepts a frame whose theme id IS the active theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still accepts a frame whose theme id IS the active theme")
val body = "<div>first parent body</div>"
var comp = _registered_compositor(body)
expect(comp.require_external_web_frame(1)).to_be(true)
val revision = simple_web_content_revision_with_theme(
    default_theme_id(), "First", body, 104, 80, 0
)
expect(comp.set_external_web_frame(1, _frame("1", revision, default_theme_id()))).to_be(true)
```

</details>

#### the owned-transfer door enforces the same theme identity

- the owned-transfer door enforces the same theme identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the owned-transfer door enforces the same theme identity")
val body = "<div>first parent body</div>"
var comp = _registered_compositor(body)
expect(comp.require_external_web_frame(1)).to_be(true)
val revision = simple_web_content_revision_with_theme(
    default_theme_id(), "First", body, 104, 80, 0
)
val hostile = _frame("1", revision, "attacker-theme-never-installed")
expect(comp.set_external_web_frame_owned(1, hostile)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/external_web_frame_theme_identity_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering external Web frame acceptance is theme-identity gated, detection: the guard must not be bypassable, and must not over-reject.
- external Web frame acceptance is theme-identity gated
- detection: the guard must not be bypassable, and must not over-reject

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

- Canonical SPipe generation for source `4174c4a85e5b92e4606ef435f90a7d4a426bdfdc414193bd6a738e7245c1cef8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4174c4a85e5b92e4606ef435f90a7d4a426bdfdc414193bd6a738e7245c1cef8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4174c4a85e5b92e4606ef435f90a7d4a426bdfdc414193bd6a738e7245c1cef8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/external_web_frame_theme_identity_guard_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/external_web_frame_theme_identity_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/external_web_frame_theme_identity_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/external_web_frame_theme_identity_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/external_web_frame_theme_identity_guard_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a frame carrying a theme id that is not the active theme' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/external_web_frame_theme_identity_guard_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a frame carrying no theme id at all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/external_web_frame_theme_identity_guard_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still accepts a frame whose theme id IS the active theme' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
