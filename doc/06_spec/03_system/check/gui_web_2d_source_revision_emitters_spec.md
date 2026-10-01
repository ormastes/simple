# GUI/Web/2D Source Revision Emitters

> Validates that upstream GUI/Web/2D evidence producers emit source-revision fields consumed by the platform freshness checker. Without these fields the freshness producer can only pass synthetic envs and real wrapper output remains too weak for final same-revision completion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI/Web/2D Source Revision Emitters

Validates that upstream GUI/Web/2D evidence producers emit source-revision fields consumed by the platform freshness checker. Without these fields the freshness producer can only pass synthetic envs and real wrapper output remains too weak for final same-revision completion.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_web_2d_source_revision_emitters_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that upstream GUI/Web/2D evidence producers emit source-revision
fields consumed by the platform freshness checker. Without these fields the
freshness producer can only pass synthetic envs and real wrapper output remains
too weak for final same-revision completion.

**Plan:** doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_source_revision_emitters_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- HTML/CSS full rendering status emits `html_css_full_rendering_goal_source_revision`.
- Production GUI/Web parity emits `production_gui_web_renderer_parity_source_revision`.
- Tauri mobile parity emits `tauri_mobile_renderer_parity_source_revision`.
- Native RenderDoc aggregate emits `native_render_log_platform_matrix_source_revision`.
- Every producer also emits the shared fallback key
  `gui_web_2d_evidence_source_revision`.
- The shell producers honor `GUI_WEB_2D_SOURCE_REVISION` when supplied so a
  platform operator can pin a final review window explicitly.

## Evidence Boundary

This SSpec checks source contracts and one lightweight HTML/CSS smoke path. It
does not launch GUI platform captures, Tauri mobile runs, production parity, or
RenderDoc aggregate capture checks.

## Producer Mapping

The freshness checker reads six upstream evidence families. Two retained
performance families already emitted source revisions before this spec was
added: `gui_showcase_4k_200fps_source_revision` and
`gui_showcase_8k_perf_source_revision`. This contract covers the four remaining
families:

- native RenderDoc aggregate:
  `native_render_log_platform_matrix_source_revision`
- Tauri mobile renderer parity:
  `tauri_mobile_renderer_parity_source_revision`
- full HTML/CSS rendering goal:
  `html_css_full_rendering_goal_source_revision`
- production GUI/Web renderer parity:
  `production_gui_web_renderer_parity_source_revision`

Every producer also emits `gui_web_2d_evidence_source_revision`. That shared
fallback lets future wrappers participate in the freshness checker before they
grow a lane-specific key.

## Source Selection

Final platform operators can set `GUI_WEB_2D_SOURCE_REVISION` to pin a review
window explicitly. If it is not set, shell wrappers try the current jj revision,
then the current git revision, then `unknown`. The native RenderDoc aggregate
uses the same environment override and VCS fallback from its embedded Python
collector. The explicit override is tested on the lightweight HTML/CSS wrapper
because it does not need platform tools to run.

## Why This Matters

The platform evidence bundle can only prove `cross-platform-freshness` when the
freshness checker sees source revisions from every lane. Without these producer
fields, a real Linux/macOS/Windows/iOS/Android run would still appear missing or
too weak even if the underlying capture artifacts existed. This contract
therefore moves the goal forward by making real wrapper output consumable by
the freshness layer.

## Manual Run Steps

1. Set `GUI_WEB_2D_SOURCE_REVISION` to the source revision shared by the final
   platform evidence window.
2. Run the native aggregate, Tauri mobile parity, retained performance,
   HTML/CSS, and production parity wrappers.
3. Confirm each generated env contains either a lane-specific source key or
   `gui_web_2d_evidence_source_revision`.
4. Run `scripts/check/check-gui-web-2d-platform-freshness.shs` against those
   env files.
5. Run `scripts/check/check-gui-web-2d-platform-evidence-bundle.shs` with the
   freshness env.

## Regression Risks

The main regression risk is a producer emitting a status without source
identity, causing final completion to rely on stale or mixed evidence. Another
risk is computing incompatible source revisions across wrappers. The explicit
`GUI_WEB_2D_SOURCE_REVISION` override is the operational escape hatch for final
platform runs because it makes the review window stable across hosts and
wrappers.

## Output Contract

The emitted source revision fields are plain env keys, not reports or prose.
They must remain machine-readable because the freshness checker reads them with
simple key lookup and does not parse generated Markdown.

## Scenarios

### GUI/Web/2D source revision emitters

#### keeps upstream producer source-revision keys available for freshness

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps upstream producer source-revision keys available for freshness


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps upstream producer source-revision keys available for freshness")
val native = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")
val mobile = file_read("scripts/check/check-tauri-mobile-renderer-parity-evidence.shs")
val production = file_read("scripts/check/check-production-gui-web-renderer-parity-evidence.shs")
val html_css = file_read("scripts/check/check-html-css-full-rendering-goal-status.shs")

expect(native).to_contain("native_render_log_platform_matrix_source_revision")
expect(native).to_contain("gui_web_2d_evidence_source_revision")
expect(native).to_contain("GUI_WEB_2D_SOURCE_REVISION")
expect(mobile).to_contain("tauri_mobile_renderer_parity_source_revision")
expect(mobile).to_contain("gui_web_2d_evidence_source_revision")
expect(mobile).to_contain("GUI_WEB_2D_SOURCE_REVISION")
expect(production).to_contain("production_gui_web_renderer_parity_source_revision")
expect(production).to_contain("gui_web_2d_evidence_source_revision")
expect(production).to_contain("GUI_WEB_2D_SOURCE_REVISION")
expect(html_css).to_contain("html_css_full_rendering_goal_source_revision")
expect(html_css).to_contain("gui_web_2d_evidence_source_revision")
expect(html_css).to_contain("GUI_WEB_2D_SOURCE_REVISION")
```

</details>

#### emits the explicit source revision in the lightweight HTML/CSS status path

- emits the explicit source revision in the lightweight HTML/CSS status path
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits the explicit source revision in the lightweight HTML/CSS status path")
val command = "rm -rf build/test-gui-web-2d-source-revision-html-css && GUI_WEB_2D_SOURCE_REVISION=rev-explicit BUILD_DIR=build/test-gui-web-2d-source-revision-html-css/out REPORT_PATH=build/test-gui-web-2d-source-revision-html-css/report.md sh scripts/check/check-html-css-full-rendering-goal-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-source-revision-html-css/out/evidence.env")
expect(evidence).to_contain("html_css_full_rendering_goal_source_revision=rev-explicit")
expect(evidence).to_contain("gui_web_2d_evidence_source_revision=rev-explicit")
```

</details>

#### reflects a different explicit source revision value (sabotage control, proves the field is not hardcoded)

- reflects a different explicit source revision value (sabotage control, proves the field is not hardcoded)
- Re-run with a different GUI_WEB_2D_SOURCE_REVISION override
   - Expected: code2 equals `0`
   - Expected: evidence2 does not contain `rev-explicit=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reflects a different explicit source revision value (sabotage control, proves the field is not hardcoded)")
step("Re-run with a different GUI_WEB_2D_SOURCE_REVISION override")
val command2 = "rm -rf build/test-gui-web-2d-source-revision-html-css-alt && GUI_WEB_2D_SOURCE_REVISION=rev-explicit-alt BUILD_DIR=build/test-gui-web-2d-source-revision-html-css-alt/out REPORT_PATH=build/test-gui-web-2d-source-revision-html-css-alt/report.md sh scripts/check/check-html-css-full-rendering-goal-status.shs || true"
val (_stdout2, _stderr2, code2) = process_run("/bin/sh", ["-c", command2])
expect(code2).to_equal(0)

val evidence2 = file_read("build/test-gui-web-2d-source-revision-html-css-alt/out/evidence.env")
expect(evidence2).to_contain("html_css_full_rendering_goal_source_revision=rev-explicit-alt")
expect(evidence2).to_contain("gui_web_2d_evidence_source_revision=rev-explicit-alt")
expect(evidence2.contains("rev-explicit=")).to_equal(false)
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


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md`
- **Design:** `doc/07_guide/tooling/renderdoc_capture_infra.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e561231f9f3f2d6824bb6352e9a929e11bb1b33799b83c9e0444dcf09eb053fc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e561231f9f3f2d6824bb6352e9a929e11bb1b33799b83c9e0444dcf09eb053fc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e561231f9f3f2d6824bb6352e9a929e11bb1b33799b83c9e0444dcf09eb053fc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/gui_web_2d_source_revision_emitters_spec.spl
mirror: doc/06_spec/03_system/check/gui_web_2d_source_revision_emitters_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_web_2d_source_revision_emitters_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_web_2d_source_revision_emitters_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_web_2d_source_revision_emitters_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/gui_web_2d_source_revision_emitters_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps upstream producer source-revision keys available for freshness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_web_2d_source_revision_emitters_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the explicit source revision in the lightweight HTML/CSS status path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_web_2d_source_revision_emitters_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reflects a different explicit source revision value (sabotage control, proves the field is not hardcoded)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
