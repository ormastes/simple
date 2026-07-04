# Feature: GUI Web 2D Vulkan RenderDoc Animation Coverage

## Raw Request
completely impl and compare chrome with simple web rendering, electron with simpel gui rendering. which all backed by vulkan with renderdoc. check all html and css elements. including animations. check next docs.   - doc/08_tracking/bug/gui_web_2d_vulkan_renderdoc_blockers_2026-06-23.md:1: requires valid .rdc captures with RDOC
    magic for Simple Vulkan Engine2D, Chrome Vulkan, and Electron Chromium/Vulkan.

  - doc/08_tracking/bug/gui_web_2d_vulkan_browser_backing_2026-06-23.md:1: pixel parity is not enough; Electron and
    Chrome must both prove Vulkan-backed GPU feature status, with no angle=vulkan unavailable logs.

  - doc/08_tracking/bug/gui_web_2d_vulkan_pairwise_aggregate_2026-06-22.md:1: prior pixel comparison passed, but
    browser/RenderDoc completion was still blocked.

Follow-up: check spipe skill of dev and use the dev skill to doc, test.

## Task Type
feature

## Refined Goal
Make the GUI/web/2D Vulkan RenderDoc verification lane explicitly prove or block Chrome, Electron, and Simple rendering parity for full HTML/CSS scope, including a separately reported animation/transition/transform CSS sub-goal.

## Acceptance Criteria
- AC-1: `scripts/check/check-html-css-full-rendering-goal-status.shs` emits machine-checkable `html_css_full_rendering_goal_animation_css_*` keys for animation, transition, and transform CSS coverage.
- AC-2: The animation CSS sub-goal reports `incomplete` with rendered count `0`, total count `18`, and the unrendered property list while those properties remain only in unsupported inventory.
- AC-3: `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` re-emits the animation CSS evidence keys and includes `CSS animation/transition/transform rendering coverage` in `blocked_completion_gates` until the sub-goal reports `pass`.
- AC-4: The existing RenderDoc/Vulkan completion contract remains fail-closed: valid `.rdc` files with `RDOC` magic, Electron and Chrome Vulkan-backed proof, and pairwise ARGB diff pass are still required before completion.
- AC-5: The focused SSpec scenario `test/03_system/check/html_css_full_rendering_goal_status_spec.spl` asserts the animation CSS evidence fields and strict-mode behavior with real command execution.
- AC-6: The mirrored generated/manual SPipe doc under `doc/06_spec/03_system/check/html_css_full_rendering_goal_status_spec.md` is regenerated and reads as an operator manual.
- AC-7: The operator guide `doc/07_guide/tooling/renderdoc_capture_infra.md` documents the animation CSS evidence keys and warns not to treat static bitmap parity as animation proof.
- AC-8: Runtime-boundary audits for working and staged changes do not report new raw env/process/runtime access introduced by this lane.

## Scope Exclusions
- This lane does not implement real CSS animation, transition, or transform rendering; it records the current gap as explicit evidence and blocks completion until a later renderer implementation closes it.
- This lane does not fabricate or relax RenderDoc, Vulkan browser backing, or pixel parity proof on hosts where Chrome, Electron, Vulkan, or RenderDoc are unavailable.

## Cooperative Review
N/A: this lane is a narrow verification-contract and documentation update with one focused SSpec; no sidecar split is needed. Merge owner: Codex. Final reviewer: normal/highest-capability Codex verification. Shared interface names: `html_css_full_rendering_goal_animation_css_*`. Manual step flow: existing `Run the full rendering goal status check without network-dependent HTML fetches`, `Read the full rendering goal evidence`, `Verify the operator report names the full CSS gap`, and `Run the same gate in strict mode`. Setup/checker helper: `scripts/check/check-html-css-full-rendering-goal-status.shs`. Fail-fast placeholders: N/A.

## Runtime Boundary Decision
- runtime_need: No new runtime capability needed.
- facade_checked: Existing `std.io_runtime` facades in the SSpec and existing shell/Python checker plumbing.
- chosen_path: reuse-facade.
- rejected_shortcuts: No raw `rt_*` aliases, no fixture-only renderer bypasses, no backend pokes, and no static bitmap parity claim as animation proof.

## Phase
dev-done

## Log
- dev: Created state file with 8 acceptance criteria (type: feature).
- spec: Updated `test/03_system/check/html_css_full_rendering_goal_status_spec.spl` with animation CSS evidence assertions.
- doc: Regenerated SPipe manual with `release/x86_64-unknown-linux-gnu/simple spipe-docgen test/03_system/check/html_css_full_rendering_goal_status_spec.spl --output doc/06_spec --no-index` (`0 stubs`) and updated the canonical stripped mirror.
- verify: `release/x86_64-unknown-linux-gnu/simple test test/03_system/check/html_css_full_rendering_goal_status_spec.spl --mode=interpreter` passed 2 scenarios.
- verify: `sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs` reported the expected incomplete RenderDoc/Vulkan state and included `CSS animation/transition/transform rendering coverage` in `blocked_completion_gates`.
- verify: `sh scripts/audit/direct-env-runtime-guard.shs --working`, `--staged`, and `find doc/06_spec -name '*_spec.spl' | wc -l` passed (`0` executable specs under `doc/06_spec`).
