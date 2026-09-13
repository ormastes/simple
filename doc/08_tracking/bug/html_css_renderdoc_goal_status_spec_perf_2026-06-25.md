# PERF BUG: HTML/CSS RenderDoc goal status spec exceeds runner threshold

## Closed 2026-09-13 — mitigation recorded and applied: 76.8s -> 11.7s, below the runner threshold
- **inferred**: the entry itself records the follow-up as done (duplicate nested traceability/manifest checks deduplicated by reusing fresh evidence) with a re-measured focused duration of 11.653s for 3 scenarios, versus the 76.783s that tripped `[PERF BUG]`.
- **measured**: `test/03_system/check/html_css_renderdoc_goal_status_spec.spl` still exists, so the speed-up was not achieved by deleting coverage.
- **inferred**: not re-timed here — the spec needs the Linux RenderDoc/GUI evidence lane, and `bin/simple test` is broken on this Windows host regardless.

## Status

- Date observed: 2026-06-25
- Spec: `test/03_system/check/html_css_renderdoc_goal_status_spec.spl`
- Observed duration: 76.783s
- Runner flag: `[PERF BUG]`
- Follow-up: reduced duplicate nested traceability/manifest checks by reusing
  fresh evidence between scenarios.
- Current focused duration: 11.653s for 3 scenarios on 2026-06-25.

## Impact

The focused RenderDoc goal status spec is useful coverage for the GUI/web/2D
evidence contract, but its synthetic nested gate setup is slow enough to trip
the system-test performance warning. This increases verification cost for the
renderer hardening lane.

## Next Investigation

- Continue monitoring if broader system-test runs flag this file again; the
  largest remaining cost is the single real traceability pass required by the
  current-state scenario.
- Keep the existing fail-closed assertions for Simple, original Chrome, and
  Electron RenderDoc evidence.
- Do not relax the Vulkan/RenderDoc evidence requirements to make the spec
  faster.
