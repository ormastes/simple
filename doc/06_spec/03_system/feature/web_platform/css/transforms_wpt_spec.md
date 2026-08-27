# Legacy CSS Transform Subset

> Proves only the existing isolated translate, uniform-scale, and quarter-turn

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Legacy CSS Transform Subset

Proves only the existing isolated translate, uniform-scale, and quarter-turn

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/transforms_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves only the existing isolated translate, uniform-scale, and quarter-turn
subset through Web style/layout, canonical Draw IR, and exact expected-color
Engine2D coverage/count. The admitted `transform-origin: 0 0` declaration is
preserved; nonzero origin application, post-layout subtree transforms,
transform-list composition, percentage bases, transformed hit testing, and
rotated/scaled text remain RED.

## Scenarios

### REQ-WEB-BROWSER-003/004: legacy CSS transform subset

#### should retain isolated axis translation

**Scenario capture:** artifact after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-BROWSER-003/004
```

</details>

#### should retain isolated uniform scale bounds

- should retain isolated uniform scale bounds
   - Artifact capture: after_step
- Resolve the admitted isolated scale through Web semantics
   - Artifact capture: after_step
- Render its exact legacy bounds through Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain isolated uniform scale bounds")
step("Resolve the admitted isolated scale through Web semantics")
step("Render its exact legacy bounds through Draw IR and Engine2D")
val html = _transform_html(
    "width:4px;height:3px;background:#2563eb;" +
    "transform-origin:0 0;transform:scale(2)"
)
expect(_transform_fingerprint(
    html, 0xFF2563EBu32
)).to_equal("block|0 0|0,0,8,6|html_ast|box:0,0,8,6|0|48")
```

</details>

#### should retain isolated quarter-turn bounds

- should retain isolated quarter-turn bounds
   - Artifact capture: after_step
- Resolve the admitted isolated quarter turn through Web semantics
   - Artifact capture: after_step
- Render its exact legacy bounds through Draw IR and Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain isolated quarter-turn bounds")
step("Resolve the admitted isolated quarter turn through Web semantics")
step("Render its exact legacy bounds through Draw IR and Engine2D")
val html = _transform_html(
    "width:6px;height:4px;background:#7c3aed;" +
    "transform-origin:0 0;transform:rotate(90deg)"
)
expect(_transform_fingerprint(
    html, 0xFF7C3AEDu32
)).to_equal("block|0 0|0,0,4,6|html_ast|box:0,0,4,6|0|24")
```

</details>

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

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003/004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26b1959b619fd0edf9f54e75d6650531e34ebe870cddabf4e9eeae8e910969c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26b1959b619fd0edf9f54e75d6650531e34ebe870cddabf4e9eeae8e910969c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26b1959b619fd0edf9f54e75d6650531e34ebe870cddabf4e9eeae8e910969c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/web_platform/css/transforms_wpt_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/transforms_wpt_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/css/transforms_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/transforms_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/transforms_wpt_spec.spl:94:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should retain isolated axis translation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/web_platform/css/transforms_wpt_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain isolated axis translation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/transforms_wpt_spec.spl:112:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain isolated uniform scale bounds' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/transforms_wpt_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain isolated uniform scale bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/transforms_wpt_spec.spl:128:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain isolated quarter-turn bounds' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/transforms_wpt_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain isolated quarter-turn bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
