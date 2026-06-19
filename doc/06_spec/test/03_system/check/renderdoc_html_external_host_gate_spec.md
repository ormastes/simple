# RenderDoc HTML external host gate

> Validates the fail-closed gate for the remaining original RenderDoc+Chrome HTML/CSS `.rdc` requirement. The local host may fail to produce a Chrome RenderDoc capture, but the gate still emits deterministic evidence that another host or CI job can satisfy.

<!-- sdn-diagram:id=renderdoc_html_external_host_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderdoc_html_external_host_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderdoc_html_external_host_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderdoc_html_external_host_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc HTML external host gate

Validates the fail-closed gate for the remaining original RenderDoc+Chrome HTML/CSS `.rdc` requirement. The local host may fail to produce a Chrome RenderDoc capture, but the gate still emits deterministic evidence that another host or CI job can satisfy.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md |
| Source | `test/03_system/check/renderdoc_html_external_host_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the fail-closed gate for the remaining original RenderDoc+Chrome
HTML/CSS `.rdc` requirement. The local host may fail to produce a Chrome
RenderDoc capture, but the gate still emits deterministic evidence that another
host or CI job can satisfy.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md
**Architecture:** N/A - environmental evidence gate.
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
RDOC_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/html/evidence.env \
BUILD_DIR=build/test-renderdoc-html-external-gate \
REPORT_PATH=build/test-renderdoc-html-external-gate/report.md \
sh scripts/check/check-renderdoc-html-external-host-gate.shs || true
```

## Examples

Passing external-host evidence must include:

```text
rdoc_backend=original
rdoc_scene=html-css-chrome
rdoc_capture_status=pass
rdoc_capture_magic=RDOC
rdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html
rdoc_chromium_requested_api=vulkan
rdoc_chromium_requested_angle=vulkan
rdoc_chromium_requested_features=Vulkan
rdoc_chromium_launch_flags=--enable-features=Vulkan --use-angle=vulkan
```

Local unavailable/fail evidence is acceptable only when it records a concrete
reason and keeps the gate status out of `pass`.

## Acceptance

- Missing or failed Chrome RenderDoc evidence produces typed non-pass gate
  evidence.
- Passing gate evidence requires original backend, the `html-css-chrome` scene,
  pass status, `RDOC` magic, the canonical HTML fixture path, and an existing
  `.rdc` file.
- Passing gate evidence requires Chromium Vulkan/ANGLE request metadata and
  launch flags.

## Scenarios

### RenderDoc HTML external host gate

#### writes typed non-pass evidence for local missing or failed Chrome capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-html-external-gate && RDOC_HTML_EVIDENCE_ENV=build/renderdoc/canonical-probe/html/evidence.env BUILD_DIR=build/test-renderdoc-html-external-gate REPORT_PATH=build/test-renderdoc-html-external-gate/report.md sh scripts/check/check-renderdoc-html-external-host-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-html-external-gate/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_html_external_gate_status=")
expect(evidence).to_contain("rdoc_html_external_gate_reason=")
expect(evidence).to_contain("rdoc_html_external_gate_source_env=")
expect(evidence).to_contain("rdoc_html_external_gate_required_backend=original")
expect(evidence).to_contain("rdoc_html_external_gate_required_scene=html-css-chrome")
expect(evidence).to_contain("rdoc_html_external_gate_required_status=pass")
expect(evidence).to_contain("rdoc_html_external_gate_required_magic=RDOC")
expect(evidence).to_contain("rdoc_html_external_gate_required_api=vulkan")
expect(evidence).to_contain("rdoc_html_external_gate_required_angle=vulkan")
expect(evidence).to_contain("rdoc_html_external_gate_required_features=Vulkan")
expect(evidence).to_contain("rdoc_html_external_gate_required_html_path_suffix=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("rdoc_html_external_gate_required_launch_flag_enable_features=--enable-features=Vulkan")
expect(evidence).to_contain("rdoc_html_external_gate_required_launch_flag_use_angle=--use-angle=vulkan")
expect(evidence).to_contain("rdoc_html_external_gate_capture_file_magic=")

val status = _value_of(evidence, "rdoc_html_external_gate_status")
val reason = _value_of(evidence, "rdoc_html_external_gate_reason")
val backend = _value_of(evidence, "rdoc_html_external_gate_backend")
val scene = _value_of(evidence, "rdoc_html_external_gate_scene")
val capture_status = _value_of(evidence, "rdoc_html_external_gate_capture_status")
val magic = _value_of(evidence, "rdoc_html_external_gate_capture_magic")
val html_path = _value_of(evidence, "rdoc_html_external_gate_html_path")
val api = _value_of(evidence, "rdoc_html_external_gate_requested_api")
val angle = _value_of(evidence, "rdoc_html_external_gate_requested_angle")
val features = _value_of(evidence, "rdoc_html_external_gate_requested_features")
val flags = _value_of(evidence, "rdoc_html_external_gate_launch_flags")

if status == "pass":
    expect(backend).to_equal("original")
    expect(scene).to_equal("html-css-chrome")
    expect(capture_status).to_equal("pass")
    expect(magic).to_equal("RDOC")
    expect(html_path).to_contain("test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
    expect(api).to_equal("vulkan")
    expect(angle).to_equal("vulkan")
    expect(features).to_contain("Vulkan")
    expect(flags).to_contain("--enable-features=Vulkan")
    expect(flags).to_contain("--use-angle=vulkan")
else:
    expect(reason.len()).to_be_greater_than(0)
```

</details>

#### passes only with controlled canonical HTML/CSS Chrome RDOC evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-html-external-gate-pass && mkdir -p build/test-renderdoc-html-external-gate-pass/source && printf 'RDOCsynthetic original html capture\\n' > build/test-renderdoc-html-external-gate-pass/source/html.rdc && printf 'rdoc_backend=original\\nrdoc_scene=html-css-chrome\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-html-external-gate-pass/source/html.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan\\n' > build/test-renderdoc-html-external-gate-pass/source/evidence.env && RDOC_HTML_EVIDENCE_ENV=build/test-renderdoc-html-external-gate-pass/source/evidence.env BUILD_DIR=build/test-renderdoc-html-external-gate-pass/out REPORT_PATH=build/test-renderdoc-html-external-gate-pass/report.md sh scripts/check/check-renderdoc-html-external-host-gate.shs"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-html-external-gate-pass/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_html_external_gate_status=pass")
expect(evidence).to_contain("rdoc_html_external_gate_reason=pass")
expect(evidence).to_contain("rdoc_html_external_gate_backend=original")
expect(evidence).to_contain("rdoc_html_external_gate_scene=html-css-chrome")
expect(evidence).to_contain("rdoc_html_external_gate_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_html_external_gate_capture_file_magic=RDOC")
expect(evidence).to_contain("rdoc_html_external_gate_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html")
expect(evidence).to_contain("rdoc_html_external_gate_requested_api=vulkan")
expect(evidence).to_contain("rdoc_html_external_gate_requested_angle=vulkan")
expect(evidence).to_contain("rdoc_html_external_gate_requested_features=Vulkan")
expect(evidence).to_contain("rdoc_html_external_gate_launch_flags=--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan")
```

</details>

#### rejects Chrome captures whose file header is not RDOC

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-html-external-gate-bad-file-magic && mkdir -p build/test-renderdoc-html-external-gate-bad-file-magic/source && printf 'NOPEsynthetic original html capture\\n' > build/test-renderdoc-html-external-gate-bad-file-magic/source/html.rdc && printf 'rdoc_backend=original\\nrdoc_scene=html-css-chrome\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-html-external-gate-bad-file-magic/source/html.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\n' > build/test-renderdoc-html-external-gate-bad-file-magic/source/evidence.env && RDOC_HTML_EVIDENCE_ENV=build/test-renderdoc-html-external-gate-bad-file-magic/source/evidence.env BUILD_DIR=build/test-renderdoc-html-external-gate-bad-file-magic/out REPORT_PATH=build/test-renderdoc-html-external-gate-bad-file-magic/report.md sh scripts/check/check-renderdoc-html-external-host-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-html-external-gate-bad-file-magic/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_html_external_gate_status=fail")
expect(evidence).to_contain("rdoc_html_external_gate_reason=missing-rdoc-file-magic")
expect(evidence).to_contain("rdoc_html_external_gate_capture_magic=RDOC")
expect(evidence).to_contain("rdoc_html_external_gate_capture_file_magic=NOPE")
```

</details>

#### rejects generic original RDOC evidence that is not the HTML/CSS Chrome scene

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-html-external-gate-generic && mkdir -p build/test-renderdoc-html-external-gate-generic/source && printf 'RDOCsynthetic generic capture\\n' > build/test-renderdoc-html-external-gate-generic/source/generic.rdc && printf 'rdoc_backend=original\\nrdoc_scene=generic\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-html-external-gate-generic/source/generic.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\n' > build/test-renderdoc-html-external-gate-generic/source/evidence.env && RDOC_HTML_EVIDENCE_ENV=build/test-renderdoc-html-external-gate-generic/source/evidence.env BUILD_DIR=build/test-renderdoc-html-external-gate-generic/out REPORT_PATH=build/test-renderdoc-html-external-gate-generic/report.md sh scripts/check/check-renderdoc-html-external-host-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-html-external-gate-generic/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_html_external_gate_status=fail")
expect(evidence).to_contain("rdoc_html_external_gate_reason=unexpected-scene")
expect(evidence).to_contain("rdoc_html_external_gate_required_scene=html-css-chrome")
```

</details>

#### rejects Chrome captures missing the Vulkan ANGLE launch flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-html-external-gate-missing-angle && mkdir -p build/test-renderdoc-html-external-gate-missing-angle/source && printf 'RDOCsynthetic original html capture\\n' > build/test-renderdoc-html-external-gate-missing-angle/source/html.rdc && printf 'rdoc_backend=original\\nrdoc_scene=html-css-chrome\\nrdoc_capture_status=pass\\nrdoc_capture_reason=pass\\nrdoc_capture_file=build/test-renderdoc-html-external-gate-missing-angle/source/html.rdc\\nrdoc_capture_magic=RDOC\\nrdoc_html_path=test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html\\nrdoc_chromium_requested_api=vulkan\\nrdoc_chromium_requested_angle=vulkan\\nrdoc_chromium_requested_features=Vulkan\\nrdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan\\n' > build/test-renderdoc-html-external-gate-missing-angle/source/evidence.env && RDOC_HTML_EVIDENCE_ENV=build/test-renderdoc-html-external-gate-missing-angle/source/evidence.env BUILD_DIR=build/test-renderdoc-html-external-gate-missing-angle/out REPORT_PATH=build/test-renderdoc-html-external-gate-missing-angle/report.md sh scripts/check/check-renderdoc-html-external-host-gate.shs || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-html-external-gate-missing-angle/out/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_html_external_gate_status=fail")
expect(evidence).to_contain("rdoc_html_external_gate_reason=missing-vulkan-angle-flag")
expect(evidence).to_contain("rdoc_html_external_gate_required_launch_flag_use_angle=--use-angle=vulkan")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md](doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md)


</details>
