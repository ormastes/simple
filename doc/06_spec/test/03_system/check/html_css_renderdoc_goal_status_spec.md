# HTML/CSS RenderDoc goal status gate

> Validates the aggregate status gate for the full HTML/CSS traceability and RenderDoc objective. The current local host should report completed traceability and Simple RenderDoc evidence while failing closed on the missing original Chrome HTML/CSS RenderDoc `.rdc` evidence.

<!-- sdn-diagram:id=html_css_renderdoc_goal_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_css_renderdoc_goal_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_css_renderdoc_goal_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_css_renderdoc_goal_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML/CSS RenderDoc goal status gate

Validates the aggregate status gate for the full HTML/CSS traceability and RenderDoc objective. The current local host should report completed traceability and Simple RenderDoc evidence while failing closed on the missing original Chrome HTML/CSS RenderDoc `.rdc` evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md |
| Source | `test/03_system/check/html_css_renderdoc_goal_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the aggregate status gate for the full HTML/CSS traceability and
RenderDoc objective. The current local host should report completed
traceability and Simple RenderDoc evidence while failing closed on the missing
original Chrome HTML/CSS RenderDoc `.rdc` evidence.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
BUILD_DIR=build/test-html-css-renderdoc-goal-status \
REPORT_PATH=build/test-html-css-renderdoc-goal-status/report.md \
sh scripts/check/check-html-css-renderdoc-goal-status.shs || true
```

## Acceptance

- The gate writes stable `html_css_*`, `simple_renderdoc_*`,
  `external_renderdoc_*`, and `macos_portability_*` evidence keys.
- Simple RenderDoc evidence is accepted only when `.rdc` magic is `RDOC`.
- The full goal remains failed until the original external RenderDoc gate
  passes.

## Scenarios

### HTML/CSS RenderDoc goal status gate

#### fails closed until original Chrome RenderDoc evidence passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-html-css-renderdoc-goal-status && BUILD_DIR=build/test-html-css-renderdoc-goal-status REPORT_PATH=build/test-html-css-renderdoc-goal-status/report.md sh scripts/check/check-html-css-renderdoc-goal-status.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-html-css-renderdoc-goal-status/evidence.env") ?? ""
expect(evidence).to_contain("html_css_renderdoc_goal_status=")
expect(evidence).to_contain("html_css_traceability_status=")
expect(evidence).to_contain("simple_renderdoc_status=")
expect(evidence).to_contain("external_renderdoc_status=")
expect(evidence).to_contain("macos_portability_status=")
expect(evidence).to_contain("required_external_backend=original")
expect(evidence).to_contain("required_external_status=pass")
expect(evidence).to_contain("required_external_magic=RDOC")

val goal_status = _value_of(evidence, "html_css_renderdoc_goal_status")
val goal_reason = _value_of(evidence, "html_css_renderdoc_goal_reason")
val simple_status = _value_of(evidence, "simple_renderdoc_status")
val external_status = _value_of(evidence, "external_renderdoc_status")

if goal_status == "pass":
    expect(simple_status).to_equal("pass")
    expect(external_status).to_equal("pass")
else:
    expect(goal_status).to_equal("fail")
    expect(goal_reason).to_equal("original-renderdoc-evidence-missing")
    expect(simple_status).to_equal("pass")
    expect(external_status).to_equal("unavailable")

val report = rt_file_read_text("build/test-html-css-renderdoc-goal-status/report.md") ?? ""
expect(report).to_contain("# HTML/CSS RenderDoc Goal Status")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md](doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md)


</details>
