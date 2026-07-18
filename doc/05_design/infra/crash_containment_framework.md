<!-- codex-design -->
# Detail Design: Crash Containment Framework

Date: 2026-04-03
Feature: `crash_containment_framework`

## Current Implementation Slice

### Implemented

- `src/os/crash_policy.spl`
  - platform-level policy types and defaults
- `src/app/dashboard/framework_policy.spl`
  - worker launch helper
  - supervised restart loop
  - budget-to-resource-profile mapping
- `src/app/dashboard/main.spl`
  - dashboard command routing through the framework

### Session Patch Added Today

- `process_run_with_limits()` now treats `timeout_ms = 0` as no wall timeout instead of silently injecting a 120-second default.
- `run_supervised_worker()` now uses the same limit-aware execution path as one-shot workers.
- supervised workers now retain:
  - resource-limit classification
  - captured child output on failure
  - uniform failure reporting across short and long-running dashboard commands

## Design Rules

### Rule 1

If a workload can corrupt or wedge the parent session, it runs out-of-process.

### Rule 2

If a failure is uncaught at the child boundary, the parent treats the child as dead and classifies the exit. It does not "resume as normal" inside the same fault domain.

### Rule 3

Timeout disabled means timeout disabled. It does not mean "use a hidden default".

### Rule 4

Baremetal recovery is a separate policy surface from hosted-app recovery.

## Follow-on Work

1. Lift the dashboard framework helpers into a general app launcher/supervisor module.
2. Route more hosted apps/services through the same policy path.
3. Add explicit integration/system tests for restart/quarantine behavior at the CLI boundary.
