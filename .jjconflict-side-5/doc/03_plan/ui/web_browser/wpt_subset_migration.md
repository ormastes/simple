# WPT Subset Migration Plan

Date: 2026-05-10

## Scope

This plan defines the repeatable Web Platform Tests subset path for Simple browser-renderer compatibility. Tests cover CSS selector matching, color/background rendering, @supports, transforms, animations, object-fit, sticky positioning, scrollbar, and custom properties — all validated deterministically through the fallback pixel renderer.

## Test Suite

| Spec File | Tests | Category |
|-----------|-------|----------|
| `test/03_system/feature/web_platform/css/selector_color_subset_spec.spl` | 57 | Selectors, colors, backgrounds |
| `test/03_system/feature/web_platform/css/wpt_scorecard_spec.spl` | 20 | Cross-category scorecard |
| `test/03_system/feature/web_platform/css/transforms_wpt_spec.spl` | 5 | CSS transforms |
| `test/03_system/feature/web_platform/css/animations_wpt_spec.spl` | 5 | Animation math, timing |
| `test/03_system/feature/web_platform/css/custom_properties_wpt_spec.spl` | 4 | var(), fallback, inheritance |
| `test/03_system/feature/web_platform/css/object_fit_wpt_spec.spl` | 4 | object-fit modes |
| `test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl` | 3 | @supports feature queries |
| `test/03_system/feature/web_platform/css/scrollbar_wpt_spec.spl` | 3 | Scrollbar rendering |
| `test/03_system/feature/web_platform/css/sticky_wpt_spec.spl` | 3 | Sticky positioning |
| **Total** | **104** | |

## Acceptance

- 104 WPT-shaped cases pass (100%).
- Each case renders through `render_html_to_pixels_with_viewport`.
- Each case asserts a deterministic pixel color result instead of relying on manual visual inspection.
- Unsupported WPT behaviors remain documented as gaps rather than being marked supported.

## Verification

```bash
bin/simple test test/03_system/feature/web_platform/css/  # All 9 spec files, 104 tests
```
