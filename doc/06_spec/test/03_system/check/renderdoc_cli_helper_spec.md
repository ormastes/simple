# RenderDoc CLI/helper interface evidence

> Checks that RenderDoc evidence tests use the shared CLI/helper contract instead of spelling `renderdoccmd`, Chrome flags, or output paths inline. The spec uses the test-facing helper facade and only runs the deterministic `env` command. Live capture remains an environmental check through:

<!-- sdn-diagram:id=renderdoc_cli_helper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderdoc_cli_helper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderdoc_cli_helper_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderdoc_cli_helper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc CLI/helper interface evidence

Checks that RenderDoc evidence tests use the shared CLI/helper contract instead of spelling `renderdoccmd`, Chrome flags, or output paths inline. The spec uses the test-facing helper facade and only runs the deterministic `env` command. Live capture remains an environmental check through:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md |
| Source | `test/03_system/check/renderdoc_cli_helper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks that RenderDoc evidence tests use the shared CLI/helper contract instead
of spelling `renderdoccmd`, Chrome flags, or output paths inline. The spec uses
the test-facing helper facade and only runs the deterministic `env` command.
Live capture remains an environmental check through:

```sh
scripts/tool/renderdoc-evidence.shs capture-simple
scripts/tool/renderdoc-evidence.shs capture-html
scripts/tool/renderdoc-evidence.shs capture-electron-html
```

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md
**Architecture:** N/A - shell/test infrastructure only.
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
/bin/sh -c ". test/helpers/renderdoc_capture_helper.shs; renderdoc_test_env"
```

## Examples

Expected environment evidence includes:

```text
rdoc_root=/path/to/repo
rdoc_cmd=/path/to/renderdoccmd
rdoc_output_dir=build/renderdoc/evidence
rdoc_timeout_secs=45
```

## Acceptance

- Test helpers expose the same interface as the shared CLI.
- Environment discovery emits stable `rdoc_*` key/value evidence.
- The Simple, Chrome HTML, and Electron HTML capture wrappers route through the
  shared CLI.
- Capture implementations write `evidence.env` with status, reason, and capture
  file keys.
- Electron HTML capture evidence records the requested Chromium Vulkan/ANGLE
  launch contract even when RenderDoc itself is unavailable.
- Live RenderDoc capture is left to the bounded check wrappers; this spec only
  proves that test code can reach the canonical helper interface.

## Scenarios

### RenderDoc CLI helper interface

#### prints shared environment evidence through the test helper facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = ". test/helpers/renderdoc_capture_helper.shs; renderdoc_test_env"
val (stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])

expect(code).to_equal(0)
expect(stdout).to_contain("rdoc_root=")
expect(stdout).to_contain("rdoc_home=")
expect(stdout).to_contain("rdoc_cmd=")
expect(stdout).to_contain("rdoc_chrome=")
expect(stdout).to_contain("rdoc_electron=")
expect(stdout).to_contain("rdoc_output_dir=")
expect(stdout).to_contain("rdoc_timeout_secs=")
```

</details>

#### keeps Simple, Chrome HTML, and Electron HTML RenderDoc wrappers on the shared CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val helper = rt_file_read_text("test/helpers/renderdoc_capture_helper.shs") ?? ""
val simple_wrapper = rt_file_read_text("scripts/check/check-renderdoc-vulkan-capture.shs") ?? ""
val html_wrapper = rt_file_read_text("scripts/check/check-renderdoc-html-capture.shs") ?? ""
val electron_wrapper = rt_file_read_text("scripts/check/check-renderdoc-electron-html-capture.shs") ?? ""

expect(helper).to_contain("renderdoc_test_capture_simple")
expect(helper).to_contain("renderdoc_test_capture_html")
expect(helper).to_contain("renderdoc_test_capture_electron_html")
expect(helper).to_contain("renderdoc-evidence.shs")
expect(simple_wrapper).to_contain("capture-simple")
expect(html_wrapper).to_contain("capture-html")
expect(electron_wrapper).to_contain("capture-electron-html")
```

</details>

#### keeps capture commands on an evidence.env artifact contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val common = rt_file_read_text("scripts/lib/renderdoc-evidence-common.shs") ?? ""

expect(common).to_contain("evidence.env")
expect(common).to_contain("rdoc_capture_status=")
expect(common).to_contain("rdoc_capture_reason=")
expect(common).to_contain("rdoc_capture_file=")
expect(common).to_contain("rdoc_chromium_requested_api=vulkan")
expect(common).to_contain("rdoc_chromium_requested_angle=vulkan")
expect(common).to_contain("--enable-features=Vulkan --use-angle=vulkan")
```

</details>

#### writes Electron Vulkan readiness evidence when RenderDoc is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = "rm -rf build/test-renderdoc-cli-helper-electron-unavailable && . scripts/lib/renderdoc-evidence-common.shs && root=$(pwd) && electron=$(rdoc_find_electron \"$root\" || true) && rdoc_write_electron_html_unavailable \"$root\" \"$electron\" build/test-renderdoc-cli-helper-electron-unavailable/electron-html missing-renderdoc || true"
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-renderdoc-cli-helper-electron-unavailable/electron-html/evidence.env") ?? ""
expect(evidence).to_contain("rdoc_backend=electron")
expect(evidence).to_contain("rdoc_capture_status=unavailable")
expect(evidence).to_contain("rdoc_capture_reason=missing-renderdoc")
expect(evidence).to_contain("rdoc_html_path=")
expect(evidence).to_contain("rdoc_electron=")
expect(evidence).to_contain("rdoc_electron_capture_script=")
expect(evidence).to_contain("rdoc_chromium_requested_api=vulkan")
expect(evidence).to_contain("rdoc_chromium_requested_angle=vulkan")
expect(evidence).to_contain("rdoc_chromium_requested_features=Vulkan")
expect(evidence).to_contain("rdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --enable-features=Vulkan --use-angle=vulkan")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md](doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md)


</details>
