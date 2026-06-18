# RenderDoc external host capture wrapper

> Validates the single-command wrapper for the remaining original RenderDoc+Chrome HTML/CSS `.rdc` gate. The local test runs readiness-only mode, which must not launch Chrome or repeat the known-crashing capture path.

<!-- sdn-diagram:id=renderdoc_external_host_capture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderdoc_external_host_capture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderdoc_external_host_capture_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderdoc_external_host_capture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc external host capture wrapper

Validates the single-command wrapper for the remaining original RenderDoc+Chrome HTML/CSS `.rdc` gate. The local test runs readiness-only mode, which must not launch Chrome or repeat the known-crashing capture path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md |
| Source | `test/03_system/check/renderdoc_external_host_capture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the single-command wrapper for the remaining original
RenderDoc+Chrome HTML/CSS `.rdc` gate. The local test runs readiness-only mode,
which must not launch Chrome or repeat the known-crashing capture path.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
BUILD_DIR=build/test-renderdoc-external-host-capture \
REPORT_PATH=build/test-renderdoc-external-host-capture/report.md \
sh scripts/check/check-renderdoc-external-host-capture.shs
```

## Acceptance

- Readiness-only mode writes stable `rdoc_external_host_*` evidence keys.
- Readiness-only mode records `capture-not-requested`.
- The pass requirement is explicit: original backend, pass status, and `RDOC`
  magic.

## Scenarios

### RenderDoc external host capture wrapper

#### writes readiness-only evidence without launching Chrome capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-external-host-capture && BUILD_DIR=build/test-renderdoc-external-host-capture REPORT_PATH=build/test-renderdoc-external-host-capture/report.md sh scripts/check/check-renderdoc-external-host-capture.shs"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-external-host-capture/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_external_host_capture_status=")
expect(evidence).to_contain("rdoc_external_host_capture_reason=")
expect(evidence).to_contain("rdoc_external_host_setup_status=")
expect(evidence).to_contain("rdoc_external_host_run_capture=0")
expect(evidence).to_contain("rdoc_external_host_required_backend=original")
expect(evidence).to_contain("rdoc_external_host_required_status=pass")
expect(evidence).to_contain("rdoc_external_host_required_magic=RDOC")

val status = _value_of(evidence, "rdoc_external_host_capture_status")
val reason = _value_of(evidence, "rdoc_external_host_capture_reason")
val raw_capture = _value_of(evidence, "rdoc_external_host_capture_status_raw")
val gate_status = _value_of(evidence, "rdoc_external_host_gate_status")

expect(status).to_equal("unavailable")
expect(reason).to_equal("capture-not-requested")
expect(raw_capture).to_equal("not-run")
expect(gate_status).to_equal("not-run")

val report = rt_file_read_text("build/test-renderdoc-external-host-capture/report.md") ?? ""
expect(report).to_contain("# RenderDoc External Host Capture")
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
