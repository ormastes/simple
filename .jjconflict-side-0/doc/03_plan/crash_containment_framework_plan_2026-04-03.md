<!-- codex-design -->
# Crash Containment Framework Plan

**Date:** 2026-04-03
**Feature:** `crash_containment_framework`

## Goal

Fix the dashboard crash path first, then turn that fix into the default crash
containment model for the hosted platform so one dashboard session, hosted app,
or LLM worker failure does not take down the parent session or the whole
platform. Keep bare-metal behavior simpler and stricter: panic, trap, and
watchdog escalation must lead to halt or reboot rather than desktop-style
restart semantics.

## Scope

This plan covers:

- dashboard crash remediation as the first delivery target
- failure taxonomy for hosted and bare-metal domains
- supervisor defaults and restart intensity
- resource budget defaults
- dashboard as the proving-ground implementation
- follow-on rollout into the generic launcher/runtime path
- Docker-only build, test, and verification for this workstream

This plan does not attempt to introduce catchable language exceptions.

## Design Direction

Simple should use:

- `Result<T, E>` for expected operational failures
- panic-like fail-fast exits for invariant violations and corrupted state
- supervision boundaries for recovery
- watchdogs for hang detection and whole-runtime failure

The target model is:

- Rust-style error discipline
- Erlang-style supervision
- embedded/bare-metal Rust style panic-handler escalation

## Failure Model

### Hosted Domains

- Recoverable error:
  - return `Result<T, E>`
- Non-recoverable invariant failure:
  - convert to structured crash record
  - kill only the child task/process fault domain
  - supervisor decides restart, quarantine, or escalation

### Bare-Metal Domains

- Recoverable operational failure:
  - return `Result<T, E>` when still in a trusted execution context
- Non-recoverable invariant failure:
  - trap, panic, abort, or watchdog timeout
  - do not continue in-place
  - panic handler or reset path decides halt vs reboot

## Default Policy

### Fault Domains

- User app: process
- System service: supervised task or child process
- Kernel component: kernel-resident domain
- Bare-metal app domain: watchdog/reset domain

### Restart Policy

- User app:
  - `one_for_one`
  - low restart count
  - quarantine on repeated crash
- System service:
  - `one_for_one`
  - higher restart intensity
  - escalate if restart budget is exhausted
- Kernel component:
  - no normal restart policy after invariant violation
- Bare-metal domain:
  - no desktop-style restart loop
  - reboot or halt

### Resource Defaults

- Interactive hosted apps:
  - memory cap `8192 MB`
  - thread cap `half(available_parallelism)` with floor `1`
- Dashboard session:
  - same as interactive default
- LLM worker:
  - same memory default, longer CPU/wall budgets
- Heavy workers:
  - compiler, test runner, batch indexer may opt into higher caps

## Implementation Phases

### Phase 1. Policy Core

Status: mostly present

- maintain `src/os/crash_policy.spl`
- keep fault-domain defaults, exit classification, supervisor defaults, and
  runtime budget defaults centralized
- keep bare-metal policy distinct from hosted policy

### Phase 2. Dashboard Framework Proving Ground

Status: in progress

- fix the current dashboard crash path before broad framework rollout
- isolate heavy dashboard work in child workers
- apply resource budgets uniformly to one-shot and supervised workers
- classify crashes consistently
- ensure long-running sessions do not silently inherit hidden timeout defaults
- keep the dashboard fix and all validation inside Docker/container flows

### Phase 3. Generic Launcher Integration

- lift dashboard-specific worker supervision into a generic hosted-app launcher
- attach `AppManifest` and launcher metadata to default workload profiles
- make hosted launcher use policy defaults automatically unless overridden

### Phase 4. Crash Record And Observability

- standardize crash record shape:
  - reason
  - domain
  - component
  - exit code / signal
  - restartable?
  - timestamp
- persist crash reports in the driver/runtime logging path
- expose counters for:
  - restart count
  - quarantine count
  - watchdog timeout count
  - resource-limit hits

### Phase 5. Bare-Metal Simplification

- keep bare-metal model minimal
- map panic/trap/watchdog timeout directly to:
  - halt
  - reboot
  - optional diagnostic dump before reset
- avoid trying to emulate hosted supervisor semantics after state corruption

### Phase 6. Verification

- all build/test/verification work for this plan must run in Docker containers
- do not rely on host execution for dashboard fix validation
- unit tests for:
  - fault-domain defaults
  - restart-window trimming
  - resource-budget defaults
  - limit classification
- system tests for:
  - child crash does not kill parent dashboard session
  - repeated crash causes quarantine
  - disabled wall timeout is honored
- bare-metal validation for:
  - panic handler path
  - watchdog timeout path
  - reset vs halt policy selection

## Work Breakdown

1. Fix the dashboard crash path and keep the fix in the dashboard proving-ground modules first.
2. Keep policy definitions in [`src/os/crash_policy.spl`](src/os/crash_policy.spl) as the single source of truth.
3. Finish the proving-ground path in [`src/app/dashboard/framework_policy.spl`](src/app/dashboard/framework_policy.spl).
4. Add generic launcher integration from [`src/os/desktop/app_manifest.spl`](src/os/desktop/app_manifest.spl) into a shared supervisor path.
5. Add crash-record plumbing to the Rust driver and runtime logging boundary.
6. Add bare-metal-specific panic/watchdog policy docs and tests.
7. Build, test, and validate only through Docker/container paths for this workstream.

## Acceptance Criteria

- A hosted dashboard or session worker panic does not crash the parent session.
- Repeated hosted worker crashes lead to quarantine instead of infinite restart.
- Interactive workloads default below `10 GB` memory and below full-thread saturation.
- Heavy workers can explicitly opt into larger resource budgets.
- Bare-metal panic/trap/watchdog rules are documented separately and do not reuse
  hosted-app restart semantics.

## Related Docs

- Architecture: [`doc/04_architecture/crash_containment_framework.md`](doc/04_architecture/crash_containment_framework.md)
- Bare-metal simplified model: [`doc/04_architecture/crash_containment_framework_baremetal_simplified.md`](doc/04_architecture/crash_containment_framework_baremetal_simplified.md)
- Detail design: [`doc/05_design/crash_containment_framework.md`](doc/05_design/crash_containment_framework.md)
