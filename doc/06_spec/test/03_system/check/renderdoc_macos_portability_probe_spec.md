# RenderDoc macOS portability probe

> Validates the macOS/MoltenVK portability wrapper for the HTML/CSS RenderDoc traceability lane. On non-macOS hosts the wrapper must not attempt RenderDoc captures; it must emit typed `unavailable` evidence instead.

<!-- sdn-diagram:id=renderdoc_macos_portability_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderdoc_macos_portability_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderdoc_macos_portability_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderdoc_macos_portability_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc macOS portability probe

Validates the macOS/MoltenVK portability wrapper for the HTML/CSS RenderDoc traceability lane. On non-macOS hosts the wrapper must not attempt RenderDoc captures; it must emit typed `unavailable` evidence instead.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md |
| Source | `test/03_system/check/renderdoc_macos_portability_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the macOS/MoltenVK portability wrapper for the HTML/CSS RenderDoc
traceability lane. On non-macOS hosts the wrapper must not attempt RenderDoc
captures; it must emit typed `unavailable` evidence instead.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md
**Architecture:** N/A - environmental evidence probe.
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
BUILD_DIR=build/test-renderdoc-macos-portability-probe \
REPORT_PATH=build/test-renderdoc-macos-portability-probe/report.md \
sh scripts/check/check-renderdoc-macos-portability-probe.shs
```

## Acceptance

- The probe writes `evidence.env` with stable `rdoc_macos_*` keys.
- Non-macOS hosts are classified as `unavailable` with reason
  `non-macos-host` and do not run captures.
- The generated report path is created for operator handoff.

## Scenarios

### RenderDoc macOS portability probe

#### writes typed unavailable evidence on non-macOS hosts without captures

<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-macos-portability-probe && BUILD_DIR=build/test-renderdoc-macos-portability-probe REPORT_PATH=build/test-renderdoc-macos-portability-probe/report.md sh scripts/check/check-renderdoc-macos-portability-probe.shs"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-macos-portability-probe/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_macos_probe_status=")
expect(evidence).to_contain("rdoc_macos_probe_reason=")
expect(evidence).to_contain("rdoc_macos_uname_s=")
expect(evidence).to_contain("rdoc_macos_vulkan_status=")
expect(evidence).to_contain("rdoc_macos_vulkan_driver=")
expect(evidence).to_contain("rdoc_macos_renderdoc_status=")
expect(evidence).to_contain("rdoc_macos_capture_simple_status=")
expect(evidence).to_contain("rdoc_macos_capture_html_status=")
expect(evidence).to_contain("rdoc_macos_html_gate_status=")

val host = _value_of(evidence, "rdoc_macos_uname_s")
val status = _value_of(evidence, "rdoc_macos_probe_status")
val reason = _value_of(evidence, "rdoc_macos_probe_reason")
val run_captures = _value_of(evidence, "rdoc_macos_run_captures")
val simple_status = _value_of(evidence, "rdoc_macos_capture_simple_status")
val html_status = _value_of(evidence, "rdoc_macos_capture_html_status")
val gate_status = _value_of(evidence, "rdoc_macos_html_gate_status")

if host == "Darwin":
    expect(status.len()).to_be_greater_than(0)
    expect(reason.len()).to_be_greater_than(0)
else:
    expect(status).to_equal("unavailable")
    expect(reason).to_equal("non-macos-host")
    expect(run_captures).to_equal("0")
    expect(simple_status).to_equal("not-run")
    expect(html_status).to_equal("not-run")
    expect(gate_status).to_equal("not-run")

val report = rt_file_read_text("build/test-renderdoc-macos-portability-probe/report.md") ?? ""
expect(report).to_contain("# RenderDoc macOS Portability Probe")
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
