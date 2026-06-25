# PERF BUG: HTML/CSS RenderDoc goal status spec exceeds runner threshold

## Status

- Date observed: 2026-06-25
- Spec: `test/03_system/check/html_css_renderdoc_goal_status_spec.spl`
- Observed duration: 76.783s
- Runner flag: `[PERF BUG]`

## Impact

The focused RenderDoc goal status spec is useful coverage for the GUI/web/2D
evidence contract, but its synthetic nested gate setup is slow enough to trip
the system-test performance warning. This increases verification cost for the
renderer hardening lane.

## Next Investigation

- Split heavy synthetic setup from the contract assertions, or add a reusable
  fixture/env builder that avoids repeated nested gate work.
- Keep the existing fail-closed assertions for Simple, original Chrome, and
  Electron RenderDoc evidence.
- Do not relax the Vulkan/RenderDoc evidence requirements to make the spec
  faster.
