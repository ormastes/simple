# Test Runner Single Example Failure Contract

> Validates that the minimal child test runner does not turn a child SSpec summary with example failures into a green file result just because the child process exits with code 0.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

## Overview

Validates that the minimal child test runner does not turn a child SSpec
summary with example failures into a green file result just because the child
process exits with code 0.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- A child program that prints `2 examples, 1 failures` and exits `0` is wrapped
  as `FAIL`.
- The wrapper process exits nonzero.
- The wrapper summary reports `Passed: 1` and `Failed: 1`.

## Scenario

### fails the wrapper when child output reports example failures

- Create a temporary child `.spl` that prints `2 examples, 1 failures` and
  returns `0`.
- Run it through `src/app/test_runner_new/test_runner_single.spl`.
- Assert the wrapper exits `1`, preserves the child example summary, prints
  `Passed: 1`, prints `Failed: 1`, and reports `FAIL`.

## Completion Boundary

This spec proves the minimal child runner honors child example-failure summaries.
It does not prove the broader GUI/Web/2D completion criteria are satisfied.
