# macOS GUI Live Window Evidence Spec

> Runs the macOS live GUI window evidence wrapper. On macOS this must launch the shared MDI sample through `scripts/macos-gui-run.shs`, detect a real `SimpleGui` window, capture its window rectangle, and fingerprint the capture. On non-macOS hosts it must skip explicitly so Linux CI cannot claim live macOS window evidence. Both lanes must prove the shared MDI titlebar button, body button, text input, and titlebar CSS source contract. The macOS pass lane must also prove rendered titlebar widget CSS pixels in the captured window bitmap. The wrapper must use a self-hosted Simple binary by default and must reject `src/compiler_rust/**` seed binaries before any host-gated evidence can pass.

<!-- sdn-diagram:id=macos_gui_live_window_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macos_gui_live_window_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macos_gui_live_window_evidence_spec -> std
macos_gui_live_window_evidence_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macos_gui_live_window_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS GUI Live Window Evidence Spec

Runs the macOS live GUI window evidence wrapper. On macOS this must launch the shared MDI sample through `scripts/macos-gui-run.shs`, detect a real `SimpleGui` window, capture its window rectangle, and fingerprint the capture. On non-macOS hosts it must skip explicitly so Linux CI cannot claim live macOS window evidence. Both lanes must prove the shared MDI titlebar button, body button, text input, and titlebar CSS source contract. The macOS pass lane must also prove rendered titlebar widget CSS pixels in the captured window bitmap. The wrapper must use a self-hosted Simple binary by default and must reject `src/compiler_rust/**` seed binaries before any host-gated evidence can pass.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/mdi_window_manager_gui_evidence_matrix_2026-06-13.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/macos_gui_live_window_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the macOS live GUI window evidence wrapper. On macOS this must launch the
shared MDI sample through `scripts/macos-gui-run.shs`, detect a real `SimpleGui`
window, capture its window rectangle, and fingerprint the capture. On non-macOS
hosts it must skip explicitly so Linux CI cannot claim live macOS window
evidence. Both lanes must prove the shared MDI titlebar button, body button,
text input, and titlebar CSS source contract. The macOS pass lane must also
prove rendered titlebar widget CSS pixels in the captured window bitmap. The
wrapper must use a self-hosted Simple binary by default and must reject
`src/compiler_rust/**` seed binaries before any host-gated evidence can pass.

## Examples

Run the host-gated evidence wrapper directly:

```sh
SIMPLE_LIB=src sh scripts/check/check-macos-gui-live-window-evidence.shs
```

Run the executable SSpec contract:

```sh
SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test test/03_system/gui/macos_gui_live_window_evidence_spec.spl --mode=interpreter
```

## Evidence Contract

The wrapper emits `macos_gui_live_window_evidence_simple_bin`,
`macos_gui_live_window_evidence_simple_bin_source`, and
`macos_gui_live_window_evidence_simple_bin_status` before the shared MDI and
capture fields. A valid host pass or non-macOS skip requires
`macos_gui_live_window_evidence_simple_bin_status=pass` and the selected binary
must not be under `src/compiler_rust/`. On macOS, a pass additionally requires
a real Aqua window whose structured event receipt contains keyboard input,
explicit pointer movement, and completed primary-button releases in both the
shared terminal titlebar and body control hitboxes. Press events,
right/middle-button releases, and clicks on blank window space do not satisfy
the interaction contract. A unique completion-only counter color must also be
present in the captured bitmap after every event class is positive. The typed
winit facade must propagate presentation failure; initial, updated, or periodic
present failure is release-blocking, and an updated event receipt may only be
written after successful presentation. An explicit seed override must fail with
`macos_gui_live_window_evidence_reason=simple-bin-forbidden` and
`macos_gui_live_window_evidence_release_gate_status=not-satisfied`.

## Scenario Checklist

1. Synthetic positive capture metrics are coherent:
   - width and height are positive.
   - total pixels equal width multiplied by height.
   - non-background pixels are positive and do not exceed total pixels.
   - the fixed six-decimal ratio matches the rounded pixel ratio.
2. Synthetic skip metrics are coherent:
   - width, height, total pixels, and non-background pixels are all zero.
   - the non-background ratio is exactly `0.000000`.
3. Incoherent synthetic metrics are rejected:
   - mismatched total pixel counts fail.
   - non-background overflow fails.
   - a positive sample with zero ratio fails.
   - a positive sample with the wrong ratio fails.
4. Explicit Rust seed selection is rejected:
   - `SIMPLE_BIN=src/compiler_rust/target/release/simple` exits with code 1.
   - the wrapper emits `macos_gui_live_window_evidence_status=fail`.
   - the wrapper emits `macos_gui_live_window_evidence_reason=simple-bin-forbidden`.
   - the report repeats the forbidden binary status.
5. On macOS, live evidence must pass:
   - the host reports `macos`.
   - a `SimpleGui` window is found.
   - the captured rectangle has positive width and height.
   - capture bytes, checksum, width, height, total pixels, and visible pixels
     are positive.
   - rendered titlebar CSS, fill, accent, and text pixel counters exceed their
     thresholds.
   - the GUI SMF artifact contract row is macOS release-ready.
6. On non-macOS hosts, evidence must skip:
   - the wrapper exits successfully.
   - status is `skip` with reason `requires-macos`.
   - the host OS field is present and is not `macos`.
   - all capture dimensions and pixel counts are zero.
   - release gate status remains `not-satisfied`.
   - the GUI SMF row keeps `macos_status=not-run`.

## Output Fields

The live or skip output must include:

- `macos_gui_live_window_evidence_status`
- `macos_gui_live_window_evidence_reason`
- `macos_gui_live_window_evidence_host_os`
- `macos_gui_live_window_evidence_launcher`
- `macos_gui_live_window_evidence_simple_bin`
- `macos_gui_live_window_evidence_simple_bin_source`
- `macos_gui_live_window_evidence_simple_bin_status`
- `macos_gui_live_window_evidence_sample`
- `macos_gui_live_window_evidence_mdi_titlebar_contract_status`
- `macos_gui_live_window_evidence_mdi_titlebar_button_markup_present`
- `macos_gui_live_window_evidence_mdi_titlebar_input_markup_present`
- `macos_gui_live_window_evidence_mdi_body_button_markup_present`
- `macos_gui_live_window_evidence_mdi_body_input_markup_present`
- `macos_gui_live_window_evidence_mdi_titlebar_css_present`
- `macos_gui_live_window_evidence_window_found`
- `macos_gui_live_window_evidence_window_title`
- `macos_gui_live_window_evidence_window_rect`
- `macos_gui_live_window_evidence_capture_path`
- `macos_gui_live_window_evidence_capture_bytes`
- `macos_gui_live_window_evidence_capture_cksum`
- `macos_gui_live_window_evidence_capture_width`
- `macos_gui_live_window_evidence_capture_height`
- `macos_gui_live_window_evidence_capture_total_pixels`
- `macos_gui_live_window_evidence_non_background_pixels`
- `macos_gui_live_window_evidence_non_background_ratio`
- `macos_gui_live_window_evidence_titlebar_css_pixels`
- `macos_gui_live_window_evidence_titlebar_widget_fill_pixels`
- `macos_gui_live_window_evidence_titlebar_widget_accent_pixels`
- `macos_gui_live_window_evidence_titlebar_widget_text_pixels`
- `macos_gui_live_window_evidence_completed_event_counter_pixels`
- `macos_gui_live_window_evidence_release_gate`
- `macos_gui_live_window_evidence_release_gate_status`
- `macos_gui_live_window_evidence_gui_smf_artifact_contract_status`
- `macos_gui_live_window_evidence_gui_smf_artifact_contract_row`
- `macos_gui_live_window_evidence_report_path`

## Completion Notes

This SSpec does not claim macOS Metal-backed rendering is complete from a Linux
host. A non-macOS run only proves the skip contract, shared MDI source contract,
capture metric validation helpers, and seed rejection. Full macOS completion
still requires a fresh macOS run with a live window screenshot, positive capture
metrics, self-hosted Simple provenance, and a release-ready GUI SMF artifact
row.

**Requirements:** N/A
**Plan:** doc/09_report/mdi_window_manager_gui_evidence_matrix_2026-06-13.md
**Design:** N/A
**Research:** N/A

## Scenarios

### macOS GUI live window evidence

#### validates synthetic positive capture metric coherence without macOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = "macos_gui_live_window_evidence_capture_width=7\n" +
    "macos_gui_live_window_evidence_capture_height=5\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=35\n" +
    "macos_gui_live_window_evidence_non_background_pixels=12\n" +
    "macos_gui_live_window_evidence_non_background_ratio=0.342857\n"
expect(_capture_fields_are_coherent(sample, true)).to_equal(true)
```

</details>

#### validates synthetic skip capture metric coherence without macOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = "macos_gui_live_window_evidence_capture_width=0\n" +
    "macos_gui_live_window_evidence_capture_height=0\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=0\n" +
    "macos_gui_live_window_evidence_non_background_pixels=0\n" +
    "macos_gui_live_window_evidence_non_background_ratio=0.000000\n"
expect(_capture_fields_are_coherent(sample, false)).to_equal(true)
```

</details>

#### rejects incoherent synthetic capture metrics without macOS

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mismatched_total = "macos_gui_live_window_evidence_capture_width=7\n" +
    "macos_gui_live_window_evidence_capture_height=5\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=36\n" +
    "macos_gui_live_window_evidence_non_background_pixels=12\n" +
    "macos_gui_live_window_evidence_non_background_ratio=0.342857\n"
val overflow_non_background = "macos_gui_live_window_evidence_capture_width=7\n" +
    "macos_gui_live_window_evidence_capture_height=5\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=35\n" +
    "macos_gui_live_window_evidence_non_background_pixels=36\n" +
    "macos_gui_live_window_evidence_non_background_ratio=1.028571\n"
val zero_positive_ratio = "macos_gui_live_window_evidence_capture_width=7\n" +
    "macos_gui_live_window_evidence_capture_height=5\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=35\n" +
    "macos_gui_live_window_evidence_non_background_pixels=12\n" +
    "macos_gui_live_window_evidence_non_background_ratio=0.000000\n"
val wrong_positive_ratio = "macos_gui_live_window_evidence_capture_width=7\n" +
    "macos_gui_live_window_evidence_capture_height=5\n" +
    "macos_gui_live_window_evidence_capture_total_pixels=35\n" +
    "macos_gui_live_window_evidence_non_background_pixels=12\n" +
    "macos_gui_live_window_evidence_non_background_ratio=0.999999\n"
expect(_capture_fields_are_coherent(mismatched_total, true)).to_equal(false)
expect(_capture_fields_are_coherent(overflow_non_background, true)).to_equal(false)
expect(_capture_fields_are_coherent(zero_positive_ratio, true)).to_equal(false)
expect(_capture_fields_are_coherent(wrong_positive_ratio, true)).to_equal(false)
```

</details>

#### rejects an explicit Rust seed Simple binary before host evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_evidence_with_seed(run_id)
val stdout = result[0]
val code = result[2]
expect(code).to_equal(1)
expect(stdout).to_contain("macos_gui_live_window_evidence_status=fail")
expect(stdout).to_contain("macos_gui_live_window_evidence_reason=simple-bin-forbidden")
expect(stdout).to_contain("macos_gui_live_window_evidence_simple_bin=src/compiler_rust/target/release/simple")
expect(stdout).to_contain("macos_gui_live_window_evidence_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(stdout).to_contain("macos_gui_live_window_evidence_simple_bin_status=forbidden")
expect(stdout).to_contain("macos_gui_live_window_evidence_release_gate_status=not-satisfied")
val report = file_read_text(_report_path(run_id))
expect(report).to_contain("macos_gui_live_window_evidence_status=fail")
expect(report).to_contain("macos_gui_live_window_evidence_reason=simple-bin-forbidden")
expect(report).to_contain("macos_gui_live_window_evidence_simple_bin_status=forbidden")
```

</details>

<details>
<summary>Advanced: passes on macOS and reports an explicit requires-macos skip elsewhere</summary>

#### passes on macOS and reports an explicit requires-macos skip elsewhere _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 167 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_evidence(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
val host_os = host_os()
if code != 0:
    print "macos_gui_live_window_evidence stdout: " + stdout
    print "macos_gui_live_window_evidence stderr: " + stderr
if host_os == "macos":
    expect(code).to_equal(0)
    expect(stdout).to_contain("macos_gui_live_window_evidence_status=pass")
    expect(stdout).to_contain("macos_gui_live_window_evidence_reason=pass")
    expect(stdout).to_contain("macos_gui_live_window_evidence_host_os=macos")
    expect(stdout).to_contain("macos_gui_live_window_evidence_launcher=macos-gui-run")
    expect(stdout).to_contain("macos_gui_live_window_evidence_simple_bin_status=pass")
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_simple_bin=") == "").to_equal(false)
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_simple_bin=").contains("src/compiler_rust/")).to_equal(false)
    expect(stdout).to_contain("macos_gui_live_window_evidence_sample=src/app/ui_shared_mdi/live_window.spl")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_titlebar_contract_status=pass")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_titlebar_button_markup_present=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_titlebar_input_markup_present=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_body_button_markup_present=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_body_input_markup_present=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_titlebar_css_present=true")
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_event_titlebar_click_events=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_event_body_click_events=")).to_be_greater_than(0)
    expect(stdout).to_contain("macos_gui_live_window_evidence_window_found=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_window_title=SimpleGui")
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_window_title=")).to_equal("SimpleGui")
    expect(stdout).to_contain("macos_gui_live_window_evidence_window_rect=")
    expect(_window_rect_has_positive_size(_extract_field(stdout, "macos_gui_live_window_evidence_window_rect="))).to_equal(true)
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_path=" + _build_dir(run_id) + "/simplegui-window.png")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_bytes=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_cksum=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_width=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_height=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_total_pixels=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_non_background_pixels=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_non_background_ratio=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_titlebar_css_pixels=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_titlebar_widget_fill_pixels=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_titlebar_widget_accent_pixels=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_titlebar_widget_text_pixels=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_completed_event_counter_pixels=")
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_bytes=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_cksum=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_width=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_height=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_total_pixels=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_non_background_pixels=")).to_be_greater_than(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_titlebar_css_pixels=")).to_be_greater_than(20)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_titlebar_widget_fill_pixels=")).to_be_greater_than(20)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_titlebar_widget_accent_pixels=")).to_be_greater_than(2)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_titlebar_widget_text_pixels=")).to_be_greater_than(2)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_completed_event_counter_pixels=")).to_be_greater_than(2)
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_non_background_ratio=") == "0.000000").to_equal(false)
    expect(_capture_fields_are_coherent(stdout, true)).to_equal(true)
    expect(stdout).to_contain("macos_gui_live_window_evidence_release_gate=live-macos-window-visual-proof")
    expect(stdout).to_contain("macos_gui_live_window_evidence_release_gate_status=satisfied")
    expect(stdout).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_status=pass")
    expect(stdout).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
    val smf_row = _extract_field(stdout, "macos_gui_live_window_evidence_gui_smf_artifact_contract_row=")
    expect(_gui_smf_contract_row_is_macos_release_ready(smf_row)).to_equal(true)
    val report = file_read_text(_report_path(run_id))
    expect(report).to_contain("# macOS GUI Live Window Evidence")
    expect(report).to_contain("GUI SMF artifact contract status: pass")
    expect(report).to_contain("GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
    expect(report).to_contain("GUI SMF artifact contract scope: contract-only; does not promote live macOS window evidence")
    expect(report).to_contain("Shared MDI titlebar contract status: pass")
    expect(report).to_contain("Shared MDI titlebar sample: src/app/ui_shared_mdi/live_window.spl")
    expect(report).to_contain("macos_gui_live_window_evidence_status=pass")
    expect(report).to_contain("macos_gui_live_window_evidence_simple_bin_status=pass")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_titlebar_contract_status=pass")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_titlebar_button_markup_present=true")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_titlebar_input_markup_present=true")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_body_button_markup_present=true")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_body_input_markup_present=true")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_titlebar_css_present=true")
    expect(report).to_contain("macos_gui_live_window_evidence_window_rect=")
    expect(report).to_contain("macos_gui_live_window_evidence_capture_cksum=")
    expect(report).to_contain("macos_gui_live_window_evidence_capture_total_pixels=")
    expect(report).to_contain("macos_gui_live_window_evidence_non_background_ratio=")
    expect(report).to_contain("macos_gui_live_window_evidence_titlebar_css_pixels=")
    expect(report).to_contain("macos_gui_live_window_evidence_titlebar_widget_fill_pixels=")
    expect(report).to_contain("macos_gui_live_window_evidence_titlebar_widget_accent_pixels=")
    expect(report).to_contain("macos_gui_live_window_evidence_release_gate_status=satisfied")
    expect(report).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_status=pass")
    expect(report).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
else:
    expect(code).to_equal(0)
    expect(stdout).to_contain("macos_gui_live_window_evidence_status=skip")
    expect(stdout).to_contain("macos_gui_live_window_evidence_reason=requires-macos")
    expect(stdout).to_contain("macos_gui_live_window_evidence_host_os=")
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_host_os=") == "macos").to_equal(false)
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_host_os=") == "").to_equal(false)
    expect(stdout).to_contain("macos_gui_live_window_evidence_launcher=macos-gui-run")
    expect(stdout).to_contain("macos_gui_live_window_evidence_simple_bin_status=pass")
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_simple_bin=") == "").to_equal(false)
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_simple_bin=").contains("src/compiler_rust/")).to_equal(false)
    expect(stdout).to_contain("macos_gui_live_window_evidence_sample=src/app/ui_shared_mdi/live_window.spl")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_titlebar_contract_status=pass")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_titlebar_button_markup_present=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_titlebar_input_markup_present=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_body_button_markup_present=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_body_input_markup_present=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_mdi_titlebar_css_present=true")
    expect(stdout).to_contain("macos_gui_live_window_evidence_event_titlebar_click_events=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_event_body_click_events=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_window_found=false")
    expect(stdout).to_contain("macos_gui_live_window_evidence_window_rect=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_path=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_bytes=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_cksum=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_width=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_height=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_capture_total_pixels=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_non_background_pixels=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_non_background_ratio=0.000000")
    expect(stdout).to_contain("macos_gui_live_window_evidence_titlebar_css_pixels=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_titlebar_widget_fill_pixels=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_titlebar_widget_accent_pixels=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_titlebar_widget_text_pixels=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_completed_event_counter_pixels=0")
    expect(stdout).to_contain("macos_gui_live_window_evidence_release_gate=live-macos-window-visual-proof")
    expect(stdout).to_contain("macos_gui_live_window_evidence_release_gate_status=not-satisfied")
    expect(stdout).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_status=")
    expect(stdout).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT ")
    expect(stdout).to_contain("qemu_status=not-run")
    expect(stdout).to_contain("macos_status=not-run")
    val smf_row = _extract_field(stdout, "macos_gui_live_window_evidence_gui_smf_artifact_contract_row=")
    expect(_row_field(smf_row, "macos_status") == "pass").to_equal(false)
    expect(_gui_smf_contract_row_is_non_macos_skip_ready(smf_row)).to_be(true)
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_window_title=")).to_equal("")
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_window_rect=")).to_equal("")
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_capture_path=")).to_equal("")
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_bytes=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_cksum=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_width=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_height=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_capture_total_pixels=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_non_background_pixels=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_titlebar_css_pixels=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_titlebar_widget_fill_pixels=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_titlebar_widget_accent_pixels=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_titlebar_widget_text_pixels=")).to_equal(0)
    expect(_extract_i64_field(stdout, "macos_gui_live_window_evidence_completed_event_counter_pixels=")).to_equal(0)
    expect(_extract_field(stdout, "macos_gui_live_window_evidence_non_background_ratio=")).to_equal("0.000000")
    expect(_capture_fields_are_coherent(stdout, false)).to_equal(true)
    val report = file_read_text(_report_path(run_id))
    expect(report).to_contain("# macOS GUI Live Window Evidence")
    expect(report).to_contain("macos_gui_live_window_evidence_status=skip")
    expect(report).to_contain("macos_gui_live_window_evidence_reason=requires-macos")
    expect(report).to_contain("macos_gui_live_window_evidence_simple_bin_status=pass")
    expect(report).to_contain("GUI SMF artifact contract status: ")
    expect(report).to_contain("GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT ")
    expect(report).to_contain("GUI SMF artifact contract scope: contract-only; does not promote live macOS window evidence")
    expect(report).to_contain("Shared MDI titlebar contract status: pass")
    expect(report).to_contain("Shared MDI titlebar sample: src/app/ui_shared_mdi/live_window.spl")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_titlebar_contract_status=pass")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_titlebar_button_markup_present=true")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_titlebar_input_markup_present=true")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_body_button_markup_present=true")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_body_input_markup_present=true")
    expect(report).to_contain("macos_gui_live_window_evidence_mdi_titlebar_css_present=true")
    expect(report).to_contain("macos_gui_live_window_evidence_window_rect=")
    expect(report).to_contain("macos_gui_live_window_evidence_capture_width=0")
    expect(report).to_contain("macos_gui_live_window_evidence_capture_height=0")
    expect(report).to_contain("macos_gui_live_window_evidence_capture_total_pixels=0")
    expect(report).to_contain("macos_gui_live_window_evidence_non_background_ratio=0.000000")
    expect(report).to_contain("macos_gui_live_window_evidence_titlebar_css_pixels=0")
    expect(report).to_contain("macos_gui_live_window_evidence_titlebar_widget_fill_pixels=0")
    expect(report).to_contain("macos_gui_live_window_evidence_titlebar_widget_accent_pixels=0")
    expect(report).to_contain("macos_gui_live_window_evidence_release_gate_status=not-satisfied")
    expect(report).to_contain("macos_gui_live_window_evidence_gui_smf_artifact_contract_status=")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/09_report/mdi_window_manager_gui_evidence_matrix_2026-06-13.md](doc/09_report/mdi_window_manager_gui_evidence_matrix_2026-06-13.md)


</details>
