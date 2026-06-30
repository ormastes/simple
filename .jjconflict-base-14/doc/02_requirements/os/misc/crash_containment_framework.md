<!-- codex-research -->
# Feature Requirements: Crash Containment Framework

Date: 2026-04-03
Feature: `crash_containment_framework`

## Goal

Prevent one dashboard app/session/worker crash from taking down the parent CLI, user session, or broader hosted platform, while still allowing stricter halt/reboot policy for kernel and baremetal domains.

## Functional Requirements

### REQ-001 Fault Domain Defaults

The platform shall define default fault domains for:

- user apps
- system services
- kernel components
- baremetal app domains

### REQ-002 Default Supervisor Policy

Hosted user apps and services shall default to supervised restart behavior with bounded restart intensity and quarantine after repeated crashes.

### REQ-003 Crash Classification

The framework shall classify child exits into at least:

- clean exit
- panic
- trap
- abort
- signal
- resource-limit violation

### REQ-004 Dashboard Isolation

Heavy or long-running dashboard commands shall execute in isolated child workers rather than directly in the parent dashboard/session process.

### REQ-005 Consistent Supervision Path

One-shot and long-running dashboard workers shall use the same limit-aware execution path so that resource-limit failures are captured and classified consistently.

### REQ-006 Baremetal Escalation

Baremetal domains shall not inherit hosted-app restart assumptions. Panic/trap policy shall escalate to halt or reboot according to domain type.

