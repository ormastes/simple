# RenderDoc capture infrastructure contract

> Verifies the shared RenderDoc shell infrastructure without launching a live capture. The contract keeps original RenderDoc Chrome capture and Simple in-application `rt_renderdoc_*` capture behind one CLI and one test helper facade.

<!-- sdn-diagram:id=renderdoc_capture_infra_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderdoc_capture_infra_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderdoc_capture_infra_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderdoc_capture_infra_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RenderDoc capture infrastructure contract

Verifies the shared RenderDoc shell infrastructure without launching a live capture. The contract keeps original RenderDoc Chrome capture and Simple in-application `rt_renderdoc_*` capture behind one CLI and one test helper facade.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md |
| Source | `test/01_unit/tooling/renderdoc_capture_infra_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the shared RenderDoc shell infrastructure without launching a live
capture. The contract keeps original RenderDoc Chrome capture and Simple
in-application `rt_renderdoc_*` capture behind one CLI and one test helper
facade.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/html_css_vulkan_renderdoc_probe_2026-06-17.md
**Architecture:** N/A - shell/test infrastructure only.
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
scripts/tool/renderdoc-evidence.shs env
scripts/tool/renderdoc-evidence.shs capture-simple
scripts/tool/renderdoc-evidence.shs capture-html
```

## Examples

Tests can source the facade:

```sh
. test/helpers/renderdoc_capture_helper.shs
renderdoc_test_env
renderdoc_test_capture_html
```

## Acceptance

- The shared CLI exposes `capture-simple`, `capture-html`, and
  `register-layer`.
- The shared library owns both capture implementations and `.rdc` magic
  validation.
- Capture commands write `evidence.env` with `rdoc_capture_status=` and
  `rdoc_capture_reason=`.
- Compatibility wrappers route through the shared CLI.
- The setup script owns path discovery and Vulkan layer registration.

## Notes

This spec is intentionally static. Live RenderDoc capture is environmental and
belongs in bounded check wrappers so unavailable hosts can report typed evidence
instead of destabilizing ordinary unit checks.

## Scenarios

### RenderDoc capture infrastructure

#### exposes one CLI for original HTML capture and Simple in-app capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli = source("scripts/tool/renderdoc-evidence.shs")
val common = source("scripts/lib/renderdoc-evidence-common.shs")

expect(cli).to_contain("capture-simple")
expect(cli).to_contain("capture-html")
expect(cli).to_contain("register-layer")
expect(common).to_contain("rdoc_capture_simple_vulkan")
expect(common).to_contain("rdoc_capture_html")
expect(common).to_contain("rdoc_validate_rdc_magic")
expect(common).to_contain("evidence.env")
expect(common).to_contain("rdoc_capture_status=")
expect(common).to_contain("rdoc_capture_reason=")
```

</details>

#### keeps test helpers and compatibility wrappers on the shared interface

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val helper = source("test/helpers/renderdoc_capture_helper.shs")
val vulkan_wrapper = source("scripts/check/check-renderdoc-vulkan-capture.shs")
val html_wrapper = source("scripts/check/check-renderdoc-html-capture.shs")

expect(helper).to_contain("renderdoc_test_capture_simple")
expect(helper).to_contain("renderdoc_test_capture_html")
expect(helper).to_contain("scripts/tool/renderdoc-evidence.shs")
expect(vulkan_wrapper).to_contain("scripts/tool/renderdoc-evidence.shs capture-simple")
expect(html_wrapper).to_contain("scripts/tool/renderdoc-evidence.shs capture-html")
```

</details>

#### keeps RenderDoc environment setup centralized

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val setup = source("scripts/setup/setup-renderdoc-env.shs")

expect(setup).to_contain("--check")
expect(setup).to_contain("--print")
expect(setup).to_contain("--register-vulkan-layer")
expect(setup).to_contain("rdoc_status_env")
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
