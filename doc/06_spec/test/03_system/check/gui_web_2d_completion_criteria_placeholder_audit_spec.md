# GUI/Web/2D Completion Criteria Placeholder Audit

> Validates the lightweight completion audit for the active GUI/Web/2D hardening goal. The audit fails closed while executable completion placeholders remain and exposes the remaining placeholder list for manual and parallel agent review.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

## Overview

Validates the lightweight completion audit for the active GUI/Web/2D hardening
goal. The audit must fail closed while executable completion placeholders
remain and must expose the remaining placeholder list for manual and parallel
agent review.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- The audit reports `completion-placeholders-remain` while unfinished lanes
  still exist.
- The current placeholder count is six.
- The audit identifies its assertion mode as `todo-placeholder-count`, not a
  runner workaround.
- The evidence lists the Linux Vulkan, macOS Metal, Windows D3D12, full
  HTML/CSS, production GUI/Web parity, and parallel-agent review placeholders.

## Scenario

### fails closed and lists the six remaining completion placeholders

- Run `scripts/check/check-gui-web-2d-completion-criteria-placeholders.shs`
  with `GUI_WEB_2D_COMPLETION_ALLOW_INCOMPLETE=1`.
- Assert the evidence status is `fail`.
- Assert the reason is `completion-placeholders-remain`.
- Assert `gui_web_2d_completion_criteria_todo_count=6`.
- Assert `gui_web_2d_completion_criteria_assertion_mode=todo-placeholder-count`.
- Assert the placeholder list names Linux Vulkan, macOS Metal, Windows D3D12,
  full HTML/CSS, production GUI/Web parity, and parallel-agent review.

## Completion Boundary

This spec proves that the completion audit reports the remaining work
accurately. It does not complete any rendering platform lane by itself.
