<!-- codex-research -->
# NFR Requirements: Crash Containment Framework

Date: 2026-04-03
Feature: `crash_containment_framework`

## NFR-001 Default Memory Budget

Unless explicitly overridden by workload class, hosted app/session workloads shall default to less than `10 GB` memory.

Selected target:

- default cap: `8192 MB`

## NFR-002 Heavy Workload Exception

Compiler, test-runner, and similar heavy worker profiles may exceed the default memory ceiling when explicitly selected.

## NFR-003 Default Thread Budget

Unless explicitly overridden by workload class, hosted app/session workloads shall default to no more than half of available system parallelism, with a floor of one thread.

## NFR-004 Crash Loop Resistance

Repeated child crashes shall not produce unbounded restart loops. The framework shall quarantine repeated failures after a bounded restart window.

## NFR-005 Failure Visibility

Crash containment shall preserve enough diagnostics to identify:

- exit code
- crash classification
- child stderr/stdout relevant to the failure

## NFR-006 Host Safety

Build, tests, and system verification for this feature shall run in Docker containers, not directly on the host server.

