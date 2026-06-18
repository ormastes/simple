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
| 1 | 1 | 0 | 0 |

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
rdoc_capture_status=pass
rdoc_capture_magic=RDOC
```

Local unavailable/fail evidence is acceptable only when it records a concrete
reason and keeps the gate status out of `pass`.

## Acceptance

- Missing or failed Chrome RenderDoc evidence produces typed non-pass gate
  evidence.
- Passing gate evidence requires original backend, pass status, `RDOC` magic,
  and an existing `.rdc` file.

## Scenarios

### RenderDoc HTML external host gate

#### writes typed non-pass evidence for local missing or failed Chrome capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
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
expect(evidence).to_contain("rdoc_html_external_gate_required_status=pass")
expect(evidence).to_contain("rdoc_html_external_gate_required_magic=RDOC")

val status = _value_of(evidence, "rdoc_html_external_gate_status")
val reason = _value_of(evidence, "rdoc_html_external_gate_reason")
val backend = _value_of(evidence, "rdoc_html_external_gate_backend")
val capture_status = _value_of(evidence, "rdoc_html_external_gate_capture_status")
val magic = _value_of(evidence, "rdoc_html_external_gate_capture_magic")

if status == "pass":
    expect(backend).to_equal("original")
    expect(capture_status).to_equal("pass")
    expect(magic).to_equal("RDOC")
else:
    expect(reason.len()).to_be_greater_than(0)
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
