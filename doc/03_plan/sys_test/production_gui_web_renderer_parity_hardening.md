# Production GUI Web Renderer Parity Hardening System Test Plan

## Focused Command

Run the executable SPipe spec directly:

```bash
bin/simple test/03_system/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl
```

Expected result: `4 examples, 0 failures`.

Current focused evidence uses the compiled runtime:

```bash
SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/03_system/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl --mode=interpreter --clean
```

Expected result: `6` passed examples, `0` failures.

## Assertions

- Generated HTML contains `widget-button`, `widget-image`, and the expected
  `data-action` from the real GUI button.
- Generated HTML does not contain legacy fixture markers.
- Software pixels fill the requested viewport and contain more than three
  distinct colors.
- CPU SIMD pixels match software exactly.
- Metal pixels match software exactly; on macOS the backend must resolve to
  `metal`, otherwise it may resolve to `software`.
- `tolerance_used` is false.

## Electron Generated-GUI Evidence

Run the live Electron generated-GUI comparison:

```bash
sh scripts/check/check-electron-generated-gui-web-parity-evidence.shs
```

Recorded result on 2026-06-03:

- status: `pass`
- reason: `pass`
- mismatch count: `0`
- blur/tolerance used: `false`
- watchdog teardown: recorded separately as provenance when Electron writes
  proof but host teardown needs the shell watchdog
- generated HTML: `build/electron_generated_gui_web_parity_evidence/generated-gui.html`
- Simple expected ARGB: `build/electron_generated_gui_web_parity_evidence/simple-cpu-simd-expected-argb.json`
- Electron captured ARGB: `build/electron_generated_gui_web_parity_evidence/electron-captured-argb.json`
- report: `doc/09_report/electron_generated_gui_web_parity_evidence_2026-06-03.md`

This proves the live Electron comparison path renders generated GUI HTML
directly and enforces exact pixel parity for this fixture.

Run the live Electron generated-GUI viewport matrix:

```bash
sh scripts/check/check-electron-generated-gui-web-parity-matrix-evidence.shs
```

Recorded result on 2026-06-03:

- status: `pass`
- cases: `80x64`, `96x72`, `128x96`, `160x120`
- mismatch count for each case: `0`
- checksums and weighted checksums match for each case
- blur/tolerance used for each case: `false`
- report: `doc/09_report/electron_generated_gui_web_parity_matrix_evidence_2026-06-03.md`

Run the aggregate release-style parity evidence gate:

```bash
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
```

Expected result:

- aggregate status: `pass`
- Electron/Chrome viewport matrix: `pass`
- Electron CSS/layout manifest: `pass`
- backend-executed CPU SIMD/Metal parity: `pass`
- raw Metal framebuffer readback: `pass`
- blur/tolerance used: `false`

Run the live Electron CSS/layout manifest evidence:

```bash
sh scripts/check/check-electron-simple-web-layout-manifest-evidence.shs
```

Recorded result on 2026-06-03:

- status: `pass`
- exact cases: `css_box_matrix`, `border_nested_matrix`,
  `selector_inline_box_matrix`, `attribute_selector_box_matrix`,
  `border_box_matrix`, `padding_longhand_matrix`, `border_side_matrix`,
  `overflow_hidden_matrix`, `visibility_hidden_matrix`,
  `position_absolute_matrix`, `position_right_bottom_matrix`,
  `position_overlap_matrix`, `position_z_index_matrix`, `opacity_matrix`,
  `background_shorthand_matrix`
- mismatch count for each case: `0`
- checksums and weighted checksums match for each case
- blur/tolerance used for each case: `false`
- tracked text case: `text_raster_track`
- tracked text mismatch count: currently `997`
- tracked text residuals: Chrome extra text `771`, Simple extra text `71`,
  text color delta `155`, surface geometry `0`
- tracked text blur/tolerance used: `false`
- manifest case count: `16`
- exact pass count: `15`
- tracked count: `1`
- fail count: `0`
- report: `doc/09_report/electron_simple_web_layout_manifest_evidence_2026-06-03.md`
