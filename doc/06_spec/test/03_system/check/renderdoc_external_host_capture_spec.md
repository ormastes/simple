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
| 3 | 3 | 0 | 0 |

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
- The pass requirement is explicit: original backend, `html-css-chrome` scene,
  pass status, `RDOC` magic, and canonical HTML fixture metadata.

## Scenarios

### RenderDoc external host capture wrapper

#### writes readiness-only evidence without launching Chrome capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
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
expect(evidence).to_contain("rdoc_external_host_required_scene=html-css-chrome")
expect(evidence).to_contain("rdoc_external_host_required_status=pass")
expect(evidence).to_contain("rdoc_external_host_required_magic=RDOC")
expect(evidence).to_contain("rdoc_external_host_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("rdoc_external_host_capture_file_magic=")
expect(evidence).to_contain("rdoc_external_host_gate_capture_file_magic=")

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

#### passes when supplied original RDOC evidence from an external host

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-external-host-capture-pass && mkdir -p build/test-renderdoc-external-host-capture-pass/source && printf 'RDOCsynthetic external host capture\\n' > build/test-renderdoc-external-host-capture-pass/source/synthetic.rdc && printf 'rdoc_backend=original\\nrdoc_scene=html-css-chrome\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-external-host-capture-pass/source/synthetic.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\n' > build/test-renderdoc-external-host-capture-pass/source/evidence.env && RDOC_HTML_EVIDENCE_ENV=build/test-renderdoc-external-host-capture-pass/source/evidence.env BUILD_DIR=build/test-renderdoc-external-host-capture-pass REPORT_PATH=build/test-renderdoc-external-host-capture-pass/report.md sh scripts/check/check-renderdoc-external-host-capture.shs"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-external-host-capture-pass/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_external_host_capture_status=pass")
expect(evidence).to_contain("rdoc_external_host_capture_reason=pass")
expect(evidence).to_contain("rdoc_external_host_gate_status=pass")
expect(evidence).to_contain("rdoc_external_host_gate_scene=html-css-chrome")
expect(evidence).to_contain("rdoc_external_host_gate_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("rdoc_external_host_capture_file_magic=RDOC")
expect(evidence).to_contain("rdoc_external_host_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("rdoc_external_host_required_backend=original")
expect(evidence).to_contain("rdoc_external_host_required_scene=html-css-chrome")
expect(evidence).to_contain("rdoc_external_host_required_status=pass")
expect(evidence).to_contain("rdoc_external_host_required_magic=RDOC")
expect(evidence).to_contain("rdoc_external_host_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")

val status = _value_of(evidence, "rdoc_external_host_capture_status")
val gate_status = _value_of(evidence, "rdoc_external_host_gate_status")
expect(status).to_equal("pass")
expect(gate_status).to_equal("pass")
```

</details>

#### rejects supplied external evidence whose capture file is not RDOC

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-external-host-capture-bad-file-magic && mkdir -p build/test-renderdoc-external-host-capture-bad-file-magic/source && printf 'NOPEsynthetic external host capture\\n' > build/test-renderdoc-external-host-capture-bad-file-magic/source/synthetic.rdc && printf 'rdoc_backend=original\\nrdoc_scene=html-css-chrome\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-external-host-capture-bad-file-magic/source/synthetic.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\n' > build/test-renderdoc-external-host-capture-bad-file-magic/source/evidence.env && RDOC_HTML_EVIDENCE_ENV=build/test-renderdoc-external-host-capture-bad-file-magic/source/evidence.env BUILD_DIR=build/test-renderdoc-external-host-capture-bad-file-magic REPORT_PATH=build/test-renderdoc-external-host-capture-bad-file-magic/report.md RDOC_EXTERNAL_RUN_CAPTURE=1 sh scripts/check/check-renderdoc-external-host-capture.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-external-host-capture-bad-file-magic/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_external_host_capture_status=fail")
expect(evidence).to_contain("rdoc_external_host_capture_reason=missing-rdoc-file-magic")
expect(evidence).to_contain("rdoc_external_host_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_external_host_capture_file_magic=NOPE")
expect(evidence).to_contain("rdoc_external_host_gate_status=fail")
expect(evidence).to_contain("rdoc_external_host_gate_reason=missing-rdoc-file-magic")
expect(evidence).to_contain("rdoc_external_host_gate_capture_file_magic=NOPE")
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

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md](doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md)


</details>
