# WPT Subset Migration Plan

Date: 2026-05-07

## Scope

This plan defines the first repeatable Web Platform Tests subset path for Simple browser-renderer compatibility. It starts with CSS selector and color rendering behavior that can be validated deterministically through the existing fallback pixel renderer.

## Initial Subset

- Local spec: `test/web_platform/css/selector_color_subset_spec.spl`
- Migration notes: `tools/wpt_to_spipe/README.md`
- Source-suite areas: WPT CSS selectors, CSS color parsing, and CSS background rendering basics.

## Acceptance

- At least 25 selected WPT-shaped cases run as SPipe.
- Each case renders through `render_html_to_pixels_with_viewport`.
- Each case asserts a deterministic pixel color result instead of relying on manual visual inspection.
- Unsupported WPT behaviors remain documented as gaps rather than being marked supported.

## Verification

- `bin/simple check test/web_platform/css/selector_color_subset_spec.spl`
- `bin/simple test test/web_platform/css/selector_color_subset_spec.spl --mode=interpreter --clean`
