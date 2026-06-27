# Web WM modern shell evidence wrapper

> Validates the lightweight evidence contract for the Web WM modern shell wrapper. The wrapper may fail closed when the local host cannot launch the Simple runtime or Electron, but it must still emit canonical artifact path aliases so the aggregate GUI RenderDoc audit can report precise file-status rows.

<!-- sdn-diagram:id=web_wm_modern_shell_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_wm_modern_shell_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_wm_modern_shell_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_wm_modern_shell_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web WM modern shell evidence wrapper

Validates the lightweight evidence contract for the Web WM modern shell wrapper. The wrapper may fail closed when the local host cannot launch the Simple runtime or Electron, but it must still emit canonical artifact path aliases so the aggregate GUI RenderDoc audit can report precise file-status rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md |
| Source | `test/03_system/check/web_wm_modern_shell_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the lightweight evidence contract for the Web WM modern shell wrapper.
The wrapper may fail closed when the local host cannot launch the Simple runtime
or Electron, but it must still emit canonical artifact path aliases so the
aggregate GUI RenderDoc audit can report precise file-status rows.

**Plan:** doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md
**Requirements:** N/A
**Research:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/web_wm_modern_shell_evidence_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- The wrapper emits legacy artifact keys and canonical `*_path` aliases.
- Early unavailable exits keep the artifact path rows for aggregate diagnostics.

## Scenarios

### Web WM modern shell evidence wrapper

#### keeps canonical artifact path aliases on early unavailable exits

- Inspect early-exit wrapper evidence rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-web-wm-modern-shell-evidence-path-aliases"
val command = "rm -rf " + root + " && " +
    "BUILD_DIR=" + root + " SIMPLE_CMD=/bin/false " +
    "sh scripts/check/check-web-wm-modern-shell-evidence.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/evidence.env")
step("Inspect early-exit wrapper evidence rows")
expect(evidence).to_contain("web_wm_modern_shell_evidence_status=environment-unavailable")
expect(evidence).to_contain("web_wm_modern_shell_evidence_reason=simple-runtime-preview-failed")
expect(evidence).to_contain("web_wm_modern_shell_evidence_html=" + root + "/simple_wm_modern_preview.html")
expect(evidence).to_contain("web_wm_modern_shell_evidence_html_path=" + root + "/simple_wm_modern_preview.html")
expect(evidence).to_contain("web_wm_modern_shell_evidence_argb=" + root + "/simple_wm_modern_preview_argb.json")
expect(evidence).to_contain("web_wm_modern_shell_evidence_argb_path=" + root + "/simple_wm_modern_preview_argb.json")
expect(evidence).to_contain("web_wm_modern_shell_evidence_png=" + root + "/simple_wm_modern_preview.png")
expect(evidence).to_contain("web_wm_modern_shell_evidence_png_path=" + root + "/simple_wm_modern_preview.png")
expect(evidence).to_contain("web_wm_modern_shell_evidence_audit=" + root + "/simple_wm_modern_preview_audit.json")
expect(evidence).to_contain("web_wm_modern_shell_evidence_audit_path=" + root + "/simple_wm_modern_preview_audit.json")
expect(evidence).to_contain("web_wm_modern_shell_evidence_log=" + root + "/electron_capture.log")
expect(evidence).to_contain("web_wm_modern_shell_evidence_log_path=" + root + "/electron_capture.log")
expect(evidence).to_contain("web_wm_modern_shell_evidence_interaction=" + root + "/simple_wm_modern_preview_interaction.json")
expect(evidence).to_contain("web_wm_modern_shell_evidence_interaction_path=" + root + "/simple_wm_modern_preview_interaction.json")
expect(evidence).to_contain("web_wm_modern_shell_evidence_interaction_png=" + root + "/simple_wm_modern_preview_after_interaction.png")
expect(evidence).to_contain("web_wm_modern_shell_evidence_interaction_png_path=" + root + "/simple_wm_modern_preview_after_interaction.png")
expect(evidence).to_contain("web_wm_modern_shell_evidence_interaction_log=" + root + "/electron_interaction.log")
expect(evidence).to_contain("web_wm_modern_shell_evidence_interaction_log_path=" + root + "/electron_interaction.log")
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

- **Plan:** [doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md](doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md)


</details>
