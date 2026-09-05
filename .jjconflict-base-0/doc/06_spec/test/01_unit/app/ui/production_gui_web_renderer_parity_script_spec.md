# Production Gui Web Renderer Parity Script Specification

> <details>

<!-- sdn-diagram:id=production_gui_web_renderer_parity_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=production_gui_web_renderer_parity_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

production_gui_web_renderer_parity_script_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=production_gui_web_renderer_parity_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production Gui Web Renderer Parity Script Specification

## Scenarios

### production GUI web renderer parity wrapper

#### runs the Electron layout manifest fresh by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/check-production-gui-web-renderer-parity-evidence.shs") ?? ""

expect(source).to_contain("LAYOUT_MANIFEST_RESUME=")
expect(source).to_contain("PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_MANIFEST_RESUME:-0")
expect(source).to_contain("ELECTRON_LAYOUT_MANIFEST_RESUME=\"$LAYOUT_MANIFEST_RESUME\"")
expect(source.contains("ELECTRON_LAYOUT_MANIFEST_RESUME=1")).to_equal(false)
```

</details>

#### keeps stale layout evidence reuse behind an explicit production override

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("scripts/check/check-production-gui-web-renderer-parity-evidence.shs") ?? ""

expect(source).to_contain("PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_MANIFEST_RESUME")
expect(source).to_contain("check-electron-simple-web-layout-manifest-evidence.shs")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/production_gui_web_renderer_parity_script_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- production GUI web renderer parity wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
