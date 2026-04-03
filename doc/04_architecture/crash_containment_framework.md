<!-- codex-design -->
# Architecture: Crash Containment Framework

Date: 2026-04-03
Feature: `crash_containment_framework`

## Decision

Adopt a layered containment model:

1. Rust CLI boundary normalizes fatal failures into classified exits and crash logs.
2. Hosted apps/services run in explicit child fault domains with per-workload budgets.
3. Supervisors use `one_for_one` restart with bounded restart windows and quarantine.
4. Kernel and baremetal domains escalate more aggressively than hosted apps.

## Components

### Policy Layer

File: `src/os/crash_policy.spl`

Owns:

- workload classes
- default memory/thread/process budgets
- fault-domain defaults
- restart policies
- escalation dispositions

### Launcher/Supervisor Layer

File: `src/app/dashboard/framework_policy.spl`

Owns:

- child worker launch
- environment thread throttling
- resource limits via `ulimit`
- restart window tracking
- crash classification

This is the current proving ground for the wider framework.

### Driver Safety Layer

Files:

- `src/compiler_rust/driver/src/cli/init.rs`
- `src/compiler_rust/log/src/lib.rs`

Owns:

- panic hook
- crash-file emission
- log-directory fallback

## Fault Domain Model

### Hosted User App

- boundary: process
- response to panic/resource fault: stop or quarantine that app
- response to invariant violation: quarantine

### System Service

- boundary: supervised task/process
- response: bounded restart, then quarantine/escalate

### Kernel Component

- boundary: kernel-resident
- response: halt/escalate on invariant violation

### Baremetal App Domain

- boundary: hardware/domain-local supervisor
- response: reboot or halt, not "retry in corrupted context"

## Resource Budget Model

### Default Interactive / Dashboard / LLM

- memory: `8192 MB`
- threads: `half(available_parallelism)` with floor `1`

### Heavy Workers

- compiler: may use all available threads and more memory
- test runner: higher memory/thread cap than interactive default
- batch indexer: intermediate heavy profile

## Architecture Notes

- Thread caps are advisory through environment for worker-aware runtimes and libraries.
- Memory/CPU/fd/process limits are enforced outside the child command boundary.
- Process-level containment is preferred over thread-level containment for dashboard and user-session workloads because post-panic in-process state is not trustworthy.

## Related

- Main rollout plan: [`doc/03_plan/crash_containment_framework_plan_2026-04-03.md`](/home/ormastes/dev/pub/simple/doc/03_plan/crash_containment_framework_plan_2026-04-03.md)
- Bare-metal simplified model: [`doc/04_architecture/crash_containment_framework_baremetal_simplified.md`](/home/ormastes/dev/pub/simple/doc/04_architecture/crash_containment_framework_baremetal_simplified.md)
