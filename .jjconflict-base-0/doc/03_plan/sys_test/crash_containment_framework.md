<!-- codex-design -->
# System Test Plan — Crash Containment Framework

Date: 2026-04-03
Feature: `crash_containment_framework`

## Goal

Verify that crash containment is enforced at the correct boundary:

- hosted app/session failures do not kill the parent platform session
- repeated hosted crashes trigger restart limits and quarantine
- bare-metal failures use halt/reboot/watchdog policy instead of hosted restart loops

## Target Scenarios

1. Hosted child worker panic is classified and contained to its child fault domain.
2. Parent session or launcher survives hosted child failure.
3. Restart intensity is bounded and repeated hosted failure leads to quarantine.
4. Interactive defaults remain below `10 GB` memory and below full-thread saturation.
5. Heavy profiles retain explicit higher budgets without changing hosted defaults.
6. Bare-metal profile remains single-threaded and does not inherit hosted wall-time or fd/process caps.
7. Bare-metal panic/trap policy escalates to reboot or halt rather than in-place retry.
8. Watchdog timeout is classified separately from clean exit and normal panic.

## Test Layers

### Unit Tests

- policy defaults
- exit classification
- restart-window trimming
- budget mapping
- thread-budget heuristics

### CLI / Integration Tests

- supervised worker crash and restart behavior
- quarantine after repeated worker crash
- disabled timeout behavior
- crash output capture and classification

### Bare-Metal Validation

- panic handler path records minimal diagnostics
- watchdog timeout path leads to reset-classified failure
- boot path can distinguish panic/reset cause when supported by platform

## Suggested Specs

- `test/unit/os/crash_policy_runtime_budget_spec.spl`
- `test/unit/app/dashboard_framework_policy_spec.spl`
- `test/unit/app/io/process_limits_enforcement_spec.spl`
- follow-up hosted CLI/system spec for generic launcher supervision
- follow-up bare-metal runtime spec for panic/watchdog escalation

## Acceptance Criteria

- Hosted crash containment works without relying on in-process panic recovery.
- Hosted repeated failure leads to quarantine, not infinite restart.
- Bare-metal validation proves simplified panic/watchdog policy, not hosted-app restart semantics.

## Notes

The dashboard path remains the current proving ground, but this test plan is for
the wider framework. Bare-metal verification should stay intentionally simpler
than hosted-session verification.
