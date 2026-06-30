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
| 4 | 4 | 0 | 0 |

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
- PATH `simple` fallback is opt-in for the wrapper.
- The aggregate nested Web WM run enables the opt-in fallback.
- The aggregate refreshes the default stale `simple-runtime-unavailable` Web WM
  env instead of reusing it forever.
- The aggregate treats Web WM modern shell artifacts as regular single-link
  files, not symlinks, hardlinks, or directories.

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

#### keeps PATH Simple runtime discovery opt-in and enables it from aggregate

- Inspect runtime fallback contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrapper = file_read("scripts/check/check-web-wm-modern-shell-evidence.shs")
val aggregate = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")

step("Inspect runtime fallback contract")
expect(wrapper).to_contain("ALLOW_PATH_SIMPLE_CMD")
expect(wrapper).to_contain("command -v simple")
expect(aggregate).to_contain("\"ALLOW_PATH_SIMPLE_CMD\": \"1\"")
expect(aggregate).to_contain("web_wm_modern_shell_should_refresh")
expect(aggregate).to_contain("simple-runtime-unavailable")
expect(aggregate).to_contain("allow_path_simple=1")
```

</details>

#### keeps aggregate Web WM artifact integrity wired to regular file checks

- Inspect aggregate artifact integrity wiring


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aggregate = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")

step("Inspect aggregate artifact integrity wiring")
expect(aggregate).to_contain("def regular_file_reason(value: str) -> str:")
expect(aggregate).to_contain("path.stat().st_nlink > 1")
expect(aggregate).to_contain("return \"hardlink\"")
expect(aggregate).to_contain("web_wm_modern_shell_log_path = value_of(\"web_wm_modern_shell_evidence_log_path\"")
expect(aggregate).to_contain("web_wm_modern_shell_log_file_status = regular_file_reason(web_wm_modern_shell_log_path)")
expect(aggregate).to_contain("web_wm_modern_shell_artifact_statuses = {")
expect(aggregate).to_contain("\"interaction-log\": web_wm_modern_shell_interaction_log_file_status")
expect(aggregate).to_contain("web_wm_modern_shell_artifact_integrity_status = \"pass\"")
expect(aggregate).to_contain("web_wm_modern_shell_artifact_integrity_reason = f\"web-wm-modern-shell-{artifact_name}-{artifact_status}\"")
expect(aggregate).to_contain("coverage_reason = web_wm_modern_shell_artifact_integrity_reason")
expect(aggregate).to_contain("web_wm_modern_shell_evidence_artifact_integrity_status")
expect(aggregate).to_contain("web_wm_modern_shell_evidence_artifact_integrity_reason")
```

</details>

#### reports hardlinked Web WM modern shell artifacts in aggregate evidence

- Confirm hardlinked Web WM log artifacts fail artifact integrity


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-web-wm-hardlink-artifact"
val command = "rm -rf " + root + " && mkdir -p " + root + "/artifacts " + root + "/out && " +
    "for f in html argb png audit log interaction interaction_png interaction_log; do printf '%s\\n' \"$f\" > " + root + "/artifacts/$f.dat; done && " +
    "ln " + root + "/artifacts/log.dat " + root + "/artifacts/log-hardlink.dat && " +
    "printf 'web_wm_modern_shell_evidence_status=pass\\nweb_wm_modern_shell_evidence_reason=pass\\nweb_wm_modern_shell_evidence_html_path=" + root + "/artifacts/html.dat\\nweb_wm_modern_shell_evidence_argb_path=" + root + "/artifacts/argb.dat\\nweb_wm_modern_shell_evidence_png_path=" + root + "/artifacts/png.dat\\nweb_wm_modern_shell_evidence_audit_path=" + root + "/artifacts/audit.dat\\nweb_wm_modern_shell_evidence_log_path=" + root + "/artifacts/log-hardlink.dat\\nweb_wm_modern_shell_evidence_interaction_path=" + root + "/artifacts/interaction.dat\\nweb_wm_modern_shell_evidence_interaction_png_path=" + root + "/artifacts/interaction_png.dat\\nweb_wm_modern_shell_evidence_interaction_log_path=" + root + "/artifacts/interaction_log.dat\\nweb_wm_modern_shell_evidence_width=1360\\nweb_wm_modern_shell_evidence_height=840\\nweb_wm_modern_shell_evidence_bitmap_nonblank_status=pass\\nweb_wm_modern_shell_evidence_audit_pass=pass\\nweb_wm_modern_shell_evidence_interaction_pass=pass\\nweb_wm_modern_shell_evidence_interaction_focus=pass\\nweb_wm_modern_shell_evidence_interaction_keyboard=pass\\nweb_wm_modern_shell_evidence_interaction_input=pass\\nweb_wm_modern_shell_evidence_interaction_pointer=pass\\nweb_wm_modern_shell_evidence_interaction_clicks=pass\\nweb_wm_modern_shell_evidence_interaction_event_count=8\\n' > " + root + "/webwm.env && " +
    "WEB_WM_MODERN_SHELL_EVIDENCE_ENV=" + root + "/webwm.env GUI_RENDERDOC_AGGREGATE_PRINT_ENV=0 BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs || true"
val (_stdout, _stderr, _code) = process_run("/bin/sh", ["-c", command])

val evidence = file_read(root + "/out/evidence.env")
step("Confirm hardlinked Web WM log artifacts fail artifact integrity")
expect(evidence).to_contain("web_wm_modern_shell_evidence_log_file_status=hardlink")
expect(evidence).to_contain("web_wm_modern_shell_evidence_artifact_integrity_status=fail")
expect(evidence).to_contain("web_wm_modern_shell_evidence_artifact_integrity_reason=web-wm-modern-shell-log-hardlink")
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

- **Plan:** [doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md](doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)
- **Research:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md)


</details>
