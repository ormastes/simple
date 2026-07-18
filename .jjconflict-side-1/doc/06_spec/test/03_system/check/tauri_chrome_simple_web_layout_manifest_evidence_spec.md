# Tauri/Chrome Simple Web layout manifest evidence

> Validates platform-specific evidence rows emitted by the Tauri/Chrome surface manifest wrapper used by the production GUI/Web renderer parity gate. The macOS branch must stay explicit: Darwin hosts use the native WKWebView snapshot backend and report real capture failures without falling back to fake or unimplemented evidence rows.

<!-- sdn-diagram:id=tauri_chrome_simple_web_layout_manifest_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_chrome_simple_web_layout_manifest_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_chrome_simple_web_layout_manifest_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_chrome_simple_web_layout_manifest_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri/Chrome Simple Web layout manifest evidence

Validates platform-specific evidence rows emitted by the Tauri/Chrome surface manifest wrapper used by the production GUI/Web renderer parity gate. The macOS branch must stay explicit: Darwin hosts use the native WKWebView snapshot backend and report real capture failures without falling back to fake or unimplemented evidence rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/tauri_chrome_simple_web_layout_manifest_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates platform-specific evidence rows emitted by the Tauri/Chrome surface
manifest wrapper used by the production GUI/Web renderer parity gate. The
macOS branch must stay explicit: Darwin hosts use the native WKWebView
snapshot backend and report real capture failures without falling back to
fake or unimplemented evidence rows.

**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/tauri_chrome_simple_web_layout_manifest_evidence_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- A Darwin host reports the Tauri surface backend as
  `macos-wkwebview-snapshot` and requires `swift,node`.
- The Darwin Tauri surface lane fails closed when the WKWebView snapshot
  command fails and does not claim live capture.
- Darwin evidence still identifies the Chrome surface lane as
  `chrome-live-bitmap`, so Chrome diagnostics remain separate from the missing
  Tauri/WKWebView backend.

## Scenarios

### Tauri/Chrome Simple Web layout manifest evidence

#### reports the macOS WKWebView snapshot backend as real capture evidence without claiming failed live capture

- Inspect Darwin-specific Tauri surface rows
- Confirm Chrome remains a distinct browser surface lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-tauri-chrome-layout-manifest-darwin-snapshot-fail"
val command = "rm -rf " + root + " && mkdir -p " + root + "/bin " + root + "/artifacts " + root + "/out && " +
    "printf '#!/bin/sh\\ncase \"$1\" in\\n  -s) echo Darwin ;;\\n  -m) echo arm64 ;;\\n  *) echo Darwin ;;\\nesac\\n' > " + root + "/bin/uname && chmod +x " + root + "/bin/uname && " +
    "printf '#!/bin/sh\\necho forced-wkwebview-failure >&2\\nexit 7\\n' > " + root + "/bin/swift && chmod +x " + root + "/bin/swift && " +
    "printf '<html><body>box</body></html>\\n' > " + root + "/artifacts/case.html && " +
    "printf '{\"width\":4,\"height\":4,\"format\":\"argb-u32\",\"producer\":\"fixture\",\"pixels\":[4294967295]}\\n' > " + root + "/artifacts/expected.json && " +
    "printf 'electron_simple_web_layout_manifest_status=pass\\nelectron_simple_web_layout_manifest_reason=pass\\nelectron_simple_web_layout_manifest_case_count=1\\nelectron_simple_web_layout_manifest_pass_count=1\\nelectron_simple_web_layout_manifest_fail_count=0\\nelectron_simple_web_layout_manifest_case=box\\nelectron_simple_web_layout_manifest_box_policy=exact\\ncase_box_electron_simple_web_layout_html_path=" + root + "/artifacts/case.html\\ncase_box_electron_simple_web_layout_expected_argb_path=" + root + "/artifacts/expected.json\\ncase_box_electron_simple_web_layout_width=4\\ncase_box_electron_simple_web_layout_height=4\\n' > " + root + "/layout.env && " +
    "PATH=" + root + "/bin:$PATH CHROME_CAPTURE_BIN=" + root + "/missing-chrome LAYOUT_ENV=" + root + "/layout.env BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-tauri-chrome-simple-web-layout-manifest-evidence.shs > " + root + "/stdout.env 2> " + root + "/stderr.log"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val evidence = file_read(root + "/out/evidence.env")
step("Inspect Darwin-specific Tauri surface rows")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_host_uname_s=Darwin")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_host_uname_m=arm64")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_status=fail")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_tauri_capture_status=fail")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_tauri_capture_reason=macos-wkwebview-snapshot-failed")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_tauri_capture_backend=macos-wkwebview-snapshot")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_tauri_capture_required_commands=swift,node")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_tauri_capture_missing_commands=")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_tauri_live_capture=false")

step("Confirm Chrome remains a distinct browser surface lane")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_chrome_capture_backend=chrome-live-bitmap")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_chrome_capture_status=unavailable")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_chrome_capture_reason=chrome-binary-unavailable")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_no_fake_capture=true")
expect(evidence).to_contain("tauri_chrome_simple_web_layout_manifest_blur_or_tolerance_used=false")
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

- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
