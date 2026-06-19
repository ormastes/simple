# Chrome opacity rounding policy specification

> Validates the strict policy used by the Tauri/Chrome layout manifest gate for the text-free opacity matrix. Chrome may be tracked for its known half-opacity byte rounding only when the fixture HTML, rectangle, mismatch count, expected ARGB, and captured ARGB all match the audited case.

<!-- sdn-diagram:id=chrome_opacity_rounding_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chrome_opacity_rounding_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chrome_opacity_rounding_policy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chrome_opacity_rounding_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome opacity rounding policy specification

Validates the strict policy used by the Tauri/Chrome layout manifest gate for the text-free opacity matrix. Chrome may be tracked for its known half-opacity byte rounding only when the fixture HTML, rectangle, mismatch count, expected ARGB, and captured ARGB all match the audited case.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-17.md |
| Source | `test/03_system/check/chrome_opacity_rounding_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the strict policy used by the Tauri/Chrome layout manifest gate for
the text-free opacity matrix. Chrome may be tracked for its known half-opacity
byte rounding only when the fixture HTML, rectangle, mismatch count, expected
ARGB, and captured ARGB all match the audited case.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** N/A
**Research:** doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-17.md
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/check/chrome_opacity_rounding_policy_spec.spl --clean
```

## Acceptance

- The reusable Chrome opacity-rounding validator accepts the audited half
  opacity rectangle only when it sees exactly 240 pixels.
- The accepted delta is limited to x=4..23 and y=4..15 at 96x64.
- The accepted expected/captured ARGB pair is exactly `0xff89a3e9` to
  `0xff8ba4ea`.
- Wrong captured colors, wrong HTML, wrong dimensions, or extra mismatch pixels
  fail closed.
- The production manifest routes the opacity case through
  `track-compositor-opacity-rounding` and calls the shared validator.

## Scenarios

### Chrome opacity rounding policy

#### accepts only the audited half-opacity Chrome byte rounding rectangle

- Generate a synthetic opacity fixture with the audited Chrome byte rounding
- Run the reusable Chrome opacity rounding validator
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate a synthetic opacity fixture with the audited Chrome byte rounding")
val (html_path, expected_path, captured_path) = write_opacity_fixture("0xff8ba4ea")

step("Run the reusable Chrome opacity rounding validator")
val (stdout, _stderr, code) = process_run("node", ["tools/chrome-live-bitmap/validate_opacity_rounding_delta.js", html_path, expected_path, captured_path])
expect(code).to_equal(0)
expect(stdout).to_contain("opacity_rounding_policy_status=pass")
expect(stdout).to_contain("opacity_rounding_policy_mismatch_count=240")
expect(stdout).to_contain("opacity_rounding_policy_expected_argb=0xff89a3e9")
expect(stdout).to_contain("opacity_rounding_policy_captured_argb=0xff8ba4ea")
```

</details>

#### rejects opacity deltas with the wrong captured color

- Generate an opacity fixture with the same rectangle but a wrong captured color
- Assert the validator fails closed instead of accepting an arbitrary mismatch
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate an opacity fixture with the same rectangle but a wrong captured color")
val (html_path, expected_path, captured_path) = write_opacity_fixture("0xff8ba4eb")

step("Assert the validator fails closed instead of accepting an arbitrary mismatch")
val (stdout, _stderr, code) = process_run("node", ["tools/chrome-live-bitmap/validate_opacity_rounding_delta.js", html_path, expected_path, captured_path])
expect(code).to_equal(1)
expect(stdout).to_contain("opacity_rounding_policy_status=fail")
expect(stdout).to_contain("opacity_rounding_policy_reason=unexpected-opacity-rounding-colors")
```

</details>

#### keeps the production manifest policy wired to the strict validator

- Read the manifest and Tauri/Chrome aggregate script
- Assert opacity is tracked by policy and validated by the shared tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the manifest and Tauri/Chrome aggregate script")
val manifest = file_read("tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt")
val script = file_read("scripts/check/check-tauri-chrome-simple-web-layout-manifest-evidence.shs")

step("Assert opacity is tracked by policy and validated by the shared tool")
expect(manifest).to_contain("opacity_matrix|simple-web-layout-opacity-matrix|96|64|track-compositor-opacity-rounding|")
expect(script).to_contain("accept_chrome_opacity_rounding_delta")
expect(script).to_contain("validate_opacity_rounding_delta.js")
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
- **Research:** [doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-17.md](doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-17.md)


</details>
