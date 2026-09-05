# GUI/Web/2D Source Revision Emitters

> Validates that upstream GUI/Web/2D evidence producers emit source-revision fields consumed by the platform freshness checker. Without these fields the freshness producer can only pass synthetic envs and real wrapper output remains too weak for final same-revision completion.

<!-- sdn-diagram:id=gui_web_2d_source_revision_emitters_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_web_2d_source_revision_emitters_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_web_2d_source_revision_emitters_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_web_2d_source_revision_emitters_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-gui-web-2d-source-revision-html-css && GUI_WEB_2D_SOURCE_REVISION=rev-explicit BUILD_DIR=build/test-gui-web-2d-source-revision-html-css/out REPORT_PATH=build/test-gui-web-2d-source-revision-html-css/report.md sh scripts/check/check-html-css-full-rendering-goal-status.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read("build/test-gui-web-2d-source-revision-html-css/out/evidence.env")
expect(evidence).to_contain("html_css_full_rendering_goal_source_revision=rev-explicit")
expect(evidence).to_contain("gui_web_2d_evidence_source_revision=rev-explicit")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md](doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
