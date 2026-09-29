# Showcase Launch Action Specification

> Tests covering Showcase catalog launch actions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Showcase Launch Action Specification

## Scenarios

### Showcase catalog launch actions

#### should reject widget surfaces until current runtime evidence exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject widget surfaces until current runtime evidence exists
   - Expected: require_error(standalone) equals `showcase-action-blocked:gui_widget_showcase:standalone`
   - Expected: require_error(host) equals `showcase-action-blocked:gui_widget_showcase:host_wm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject widget surfaces until current runtime evidence exists")
val standalone = parse_showcase_launch_action("showcase.launch:gui_widget_showcase:standalone")
val host = parse_showcase_launch_action("showcase.launch:gui_widget_showcase:host_wm")
expect(require_error(standalone)).to_equal("showcase-action-blocked:gui_widget_showcase:standalone")
expect(require_error(host)).to_equal("showcase-action-blocked:gui_widget_showcase:host_wm")
```

</details>

#### should reject blocked graphics surfaces

- should reject blocked graphics surfaces
   - Expected: require_error(standalone) equals `showcase-action-blocked:graphics_2d_showcase:standalone`
   - Expected: require_error(host) equals `showcase-action-blocked:graphics_2d_showcase:host_wm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject blocked graphics surfaces")
val standalone = parse_showcase_launch_action("showcase.launch:graphics_2d_showcase:standalone")
val host = parse_showcase_launch_action("showcase.launch:graphics_2d_showcase:host_wm")
expect(require_error(standalone)).to_equal("showcase-action-blocked:graphics_2d_showcase:standalone")
expect(require_error(host)).to_equal("showcase-action-blocked:graphics_2d_showcase:host_wm")
```

</details>

#### should reject blocked web surfaces

- should reject blocked web surfaces
   - Expected: require_error(standalone) equals `showcase-action-blocked:web_standards_showcase:standalone`
   - Expected: require_error(host) equals `showcase-action-blocked:web_standards_showcase:host_wm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject blocked web surfaces")
val standalone = parse_showcase_launch_action("showcase.launch:web_standards_showcase:standalone")
val host = parse_showcase_launch_action("showcase.launch:web_standards_showcase:host_wm")
expect(require_error(standalone)).to_equal("showcase-action-blocked:web_standards_showcase:standalone")
expect(require_error(host)).to_equal("showcase-action-blocked:web_standards_showcase:host_wm")
```

</details>

#### should reject every SimpleOS surface until installed evidence exists

- should reject every SimpleOS surface until installed evidence exists
   - Expected: require_error(graphics) equals `showcase-action-blocked:graphics_2d_showcase:simpleos_wm`
   - Expected: require_error(web) equals `showcase-action-blocked:web_standards_showcase:simpleos_wm`
   - Expected: require_error(widgets) equals `showcase-action-blocked:gui_widget_showcase:simpleos_wm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject every SimpleOS surface until installed evidence exists")
val graphics = parse_showcase_launch_action("showcase.launch:graphics_2d_showcase:simpleos_wm")
val web = parse_showcase_launch_action("showcase.launch:web_standards_showcase:simpleos_wm")
val widgets = parse_showcase_launch_action("showcase.launch:gui_widget_showcase:simpleos_wm")
expect(require_error(graphics)).to_equal("showcase-action-blocked:graphics_2d_showcase:simpleos_wm")
expect(require_error(web)).to_equal("showcase-action-blocked:web_standards_showcase:simpleos_wm")
expect(require_error(widgets)).to_equal("showcase-action-blocked:gui_widget_showcase:simpleos_wm")
```

</details>

#### should reject the 2d web and gui SimpleOS screen surfaces until evidence exists

- should reject the 2d web and gui SimpleOS screen surfaces until evidence exists
   - Expected: require_error(parsed) equals `showcase-action-blocked:{app_id}:{key}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject the 2d web and gui SimpleOS screen surfaces until evidence exists")
for key in ["simpleos_2d", "simpleos_web", "simpleos_gui"]:
    for app_id in ["graphics_2d_showcase", "web_standards_showcase", "gui_widget_showcase"]:
        val parsed = parse_showcase_launch_action("showcase.launch:{app_id}:{key}")
        expect(require_error(parsed)).to_equal("showcase-action-blocked:{app_id}:{key}")
```

</details>

#### should reject an unknown application

- should reject an unknown application
   - Expected: require_error(result) equals `showcase-action-unknown-app:unknown_showcase`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject an unknown application")
val result = parse_showcase_launch_action("showcase.launch:unknown_showcase:standalone")
expect(require_error(result)).to_equal("showcase-action-unknown-app:unknown_showcase")
```

</details>

#### should reject an unknown surface

- should reject an unknown surface
   - Expected: require_error(result) equals `showcase-action-unknown-surface:remote`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject an unknown surface")
val result = parse_showcase_launch_action("showcase.launch:gui_widget_showcase:remote")
expect(require_error(result)).to_equal("showcase-action-unknown-surface:remote")
```

</details>

#### should reject malformed action shapes

- should reject malformed action shapes
   - Expected: require_error(parse_showcase_launch_action("")) equals `showcase-action-malformed`
   - Expected: require_error(parse_showcase_launch_action("showcase.launch")) equals `showcase-action-malformed`
   - Expected: require_error(parse_showcase_launch_action("showcase.open:gui_widget_showcase:standalone")) equals `showcase-action-malformed`
   - Expected: require_error(parse_showcase_launch_action("showcase.launch::standalone")) equals `showcase-action-malformed`
   - Expected: require_error(parse_showcase_launch_action("showcase.launch:gui_widget_showcase:")) equals `showcase-action-malformed`
   - Expected: require_error(parse_showcase_launch_action("showcase.launch:gui_widget_showcase:standalone:extra")) equals `showcase-action-malformed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject malformed action shapes")
expect(require_error(parse_showcase_launch_action(""))).to_equal("showcase-action-malformed")
expect(require_error(parse_showcase_launch_action("showcase.launch"))).to_equal("showcase-action-malformed")
expect(require_error(parse_showcase_launch_action("showcase.open:gui_widget_showcase:standalone"))).to_equal("showcase-action-malformed")
expect(require_error(parse_showcase_launch_action("showcase.launch::standalone"))).to_equal("showcase-action-malformed")
expect(require_error(parse_showcase_launch_action("showcase.launch:gui_widget_showcase:"))).to_equal("showcase-action-malformed")
expect(require_error(parse_showcase_launch_action("showcase.launch:gui_widget_showcase:standalone:extra"))).to_equal("showcase-action-malformed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Showcase catalog launch actions.
- Showcase catalog launch actions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8a250801bc135ceb37df6cf947462e293ced4bc381a3ca229a41bdf0ecd93e65`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8a250801bc135ceb37df6cf947462e293ced4bc381a3ca229a41bdf0ecd93e65`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8a250801bc135ceb37df6cf947462e293ced4bc381a3ca229a41bdf0ecd93e65`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl
mirror: doc/06_spec/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject widget surfaces until current runtime evidence exists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject widget surfaces until current runtime evidence exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject blocked graphics surfaces' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject blocked graphics surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject blocked web surfaces' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject blocked web surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject every SimpleOS surface until installed evidence exists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject the 2d web and gui SimpleOS screen surfaces until evidence exists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/apps/showcase_catalog/showcase_launch_action_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an unknown application' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
