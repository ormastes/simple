# Electron Simple Web Layout Manifest Evidence

- manifest: tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt
- timeout seconds: 20
- run status: timed out after 240s outer cap
- blocker status: real layout divergences reached after clearing `missing-simple-bin`
- first exact failing case: `overflow_axis_matrix`
- first exact failing mismatch count: 270
- first exact failing reason: `checksum-mismatch`
- first exact failing classification: `Chrome extra text pixels=270`, no blur/tolerance
- note: the manifest did not complete all 50 cases before the outer cap, so this report is partial evidence, not a full manifest PASS/FAIL verdict.
- follow-up correction: a simple axis-only clip split was tested and worsened
  this case to 342 mismatches. The remaining evidence points at mixed-axis
  overflow computed behavior and scrollbar/auto-overflow painting, not just
  clipping the existing rectangle on one axis.
- follow-up resolution: the focused `overflow_axis_matrix` rerun now passes
  exactly after modeling mixed-axis vertical auto overflow and painting the
  scrollbar. See
  `doc/09_report/electron_simple_web_layout_overflow_axis_after_scrollbar_paint_2026-06-23.md`.
- follow-up resolution: focused current-head evidence confirmed
  `position_relative_offset_matrix` diverged with 18 geometry pixels. The
  mismatch is a 6x3 strip where Chromium keeps the relatively positioned blue
  box above the later normal-flow yellow box. A naive delayed relative repaint
  was tested and rejected because it worsened the fixture to 40 mismatches.
  The accepted fix delays the relative normal-flow paint group and now passes
  exactly. Evidence:
  `doc/09_report/electron_simple_web_layout_position_relative_offset_after_relative_group_2026-06-23.md`.

## Cases
- css_box_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-css-box-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/css_box_matrix/report.md
  - description: Text-free CSS box model matrix covering style-block selectors, content-box width/height, padding, flex row, flex column, gap, margin-left, and compound classes.
- border_nested_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-border-nested-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/border_nested_matrix/report.md
  - description: Text-free CSS border and nested selector matrix covering solid border width/color, content-box sizing with border and padding, direct-child selectors, descendant selectors, margin-top, margin-left, and out-of-scope selector rejection.
- selector_inline_box_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-selector-inline-box-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/selector_inline_box_matrix/report.md
  - description: Text-free selector and inline style matrix covering direct-child plus compound class selectors, descendant ID selectors, scoped selector rejection, and inline style precedence.
- attribute_selector_box_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-attribute-selector-box-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/attribute_selector_box_matrix/report.md
  - description: Text-free attribute selector matrix covering presence, exact value, prefix, suffix, and non-matching attribute selectors.
- pseudo_selector_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-pseudo-selector-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/pseudo_selector_matrix/report.md
  - description: Text-free pseudo-selector matrix covering :is(), :not(), :has() direct-child matching, :first-child, :last-child, and :nth-child() geometry.
- layer_nesting_structural_matrix: status=divergent reason=checksum-mismatch policy=track-css-selector-layer-divergence exit=1 mismatch=600 blur_or_tolerance=false
  - scene: simple-web-layout-layer-nesting-structural-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/layer_nesting_structural_matrix/report.md
  - description: Text-free CSS layer, nested selector normalization, and structural pseudo selector matrix covering @layer, parent-reference nesting, descendant nesting, :only-child, :empty, and nth-child formula geometry. Current Simple bitmap rendering is captured but intentionally tracked divergent against Chromium instead of claimed exact.
- border_box_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-border-box-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/border_box_matrix/report.md
  - description: Text-free box-sizing matrix covering border-box explicit outer width/height with padding and borders beside default content-box sizing.
- padding_longhand_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-padding-longhand-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/padding_longhand_matrix/report.md
  - description: Text-free padding longhand matrix covering padding-top/right/bottom/left and shorthand-plus-longhand side overrides.
- border_side_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-border-side-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/border_side_matrix/report.md
  - description: Text-free asymmetric border-side matrix covering border-left/top/right/bottom and border-width side shorthand geometry.
- overflow_hidden_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-overflow-hidden-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/overflow_hidden_matrix/report.md
  - description: Text-free overflow hidden matrix covering ancestor padding-box clipping for oversized descendants and later overflowing siblings.
- overflow_axis_matrix: status=divergent reason=checksum-mismatch policy=exact exit=1 mismatch=270 blur_or_tolerance=false
  - scene: simple-web-layout-overflow-axis-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/overflow_axis_matrix/report.md
  - description: Text-free CSS overflow axis matrix covering overflow-x:hidden, overflow-y:hidden, mixed-axis visible behavior, and both-axis clipping.
- visibility_hidden_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-visibility-hidden-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/visibility_hidden_matrix/report.md
  - description: Text-free visibility hidden matrix covering layout-preserving paint suppression for hidden boxes and inherited hidden descendants.
- display_contents_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-display-contents-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/display_contents_matrix/report.md
  - description: Text-free display contents matrix covering wrapper box suppression while preserving child layout participation.
- display_none_matrix: status=divergent reason=weighted-checksum-mismatch policy=track-css-display-none-flow-divergence exit=1 mismatch=844 blur_or_tolerance=false
  - scene: simple-web-layout-display-none-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/display_none_matrix/report.md
  - description: Text-free display none matrix covering hidden subtree paint suppression and removal from normal-flow layout before following visible blocks. Current Simple bitmap rendering is captured but intentionally tracked divergent against Chromium instead of claimed exact.
- float_clear_flowroot_matrix: status=divergent reason=checksum-mismatch policy=track-float-layout-divergence exit=1 mismatch=2202 blur_or_tolerance=false
  - scene: simple-web-layout-float-clear-flowroot-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/float_clear_flowroot_matrix/report.md
  - description: Text-free float matrix covering float:left, float:right, clear:both, display:flow-root, and overflow:hidden float containment. Current Simple float geometry is rendered and captured but intentionally tracked divergent against Chromium instead of claimed exact.
- position_absolute_matrix: status=pass reason=pass policy=exact exit=0 mismatch=0 blur_or_tolerance=false
  - scene: simple-web-layout-position-absolute-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/position_absolute_matrix/report.md
  - description: Text-free positioned layout matrix covering position:relative containing block, absolute left/top offsets, and removal from normal flow.
- position_relative_offset_matrix: status=divergent reason=checksum-mismatch policy=exact exit=1 mismatch=18 blur_or_tolerance=false
  - scene: simple-web-layout-position-relative-offset-matrix
  - dimensions: 96x64
  - report: build/electron_simple_web_layout_manifest_after_engine_dispatch/position_relative_offset_matrix/report.md
  - description: Text-free positioned layout matrix covering position:relative left/top visual offset while preserving the original normal-flow slot for following siblings and shifting descendants with the positioned box.
