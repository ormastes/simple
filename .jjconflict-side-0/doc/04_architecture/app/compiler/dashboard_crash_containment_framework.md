<!-- codex-design -->
# Architecture — Dashboard Crash Containment Framework

Date: 2026-04-03

## Overview

The framework uses a hosted-worker model for risky dashboard and LLM dashboard commands:

1. Parent command process classifies the workload.
2. Parent selects fault domain, supervisor policy, and runtime budget.
3. Parent launches a child worker with shell-enforced resource limits plus runtime budget environment variables.
4. Parent either waits once or supervises/restarts depending on workload type.
5. Crash semantics differ by app class:
   - user app: restart or quarantine
   - system service: supervised restart with higher restart intensity
   - kernel component: halt/escalate
   - bare-metal domain: reboot/halt

The immediate implementation target is the dashboard crash path. The dashboard
is the proving ground for the broader hosted-app crash containment model.

## Main Modules

- Policy model: [`src/os/crash_policy.spl`](src/os/crash_policy.spl)
- Dashboard worker launcher / supervisor: [`src/app/dashboard/framework_policy.spl`](src/app/dashboard/framework_policy.spl)
- Dashboard CLI entrypoint: [`src/app/dashboard/main.spl`](src/app/dashboard/main.spl)
- LLM dashboard entrypoint: [`src/app/llm_dashboard/main.spl`](src/app/llm_dashboard/main.spl)
- Rust watchdog and crash logging: [`src/compiler_rust/compiler/src/watchdog.rs`](src/compiler_rust/compiler/src/watchdog.rs), [`src/compiler_rust/driver/src/cli/init.rs`](src/compiler_rust/driver/src/cli/init.rs)

## Fault-Domain Rules

- Hosted user-facing work must never rely on panic recovery at the top-level session process.
- Risky dashboard work must execute in child workers.
- Parent sessions may supervise child workers, but they must not share the same failure fate.
- Kernel and bare-metal domains do not get hosted-app restart semantics after invariant failure.

## Resource Model

- Interactive default / dashboard session / LLM worker:
  - `8192 MB`
  - half available threads
- Compiler-heavy:
  - `16384 MB`
  - all available threads
- Test-runner-heavy:
  - `12288 MB`
  - all available threads
- Batch-indexer-heavy:
  - `12288 MB`
  - capped high-water mark

## Key Architectural Decision

Use outer-process containment as the primary safety boundary, with inner watchdogs and thread-pool environment hints as secondary enforcement. This matches Rust’s actual panic model better than trying to normalize panics inside the main session process.

## Verification Boundary

Dashboard crash-fix build, test, and runtime validation should stay inside
Docker/container flows for this workstream. That keeps the crash fix insulated
from host-environment drift and matches the requested deployment discipline.
