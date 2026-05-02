<!-- codex-research -->
# Feature Requirements — Dashboard Crash Containment Framework

Date: 2026-04-03
Selection basis: explicit user direction in prompt

## Functional Requirements

- REQ-F1-001: Hosted dashboard and LLM dashboard commands that can crash or exhaust resources shall run in isolated worker processes instead of the caller session process.
- REQ-F1-002: The framework shall define default fault domains for user apps, system services, kernel-resident components, and bare-metal domains.
- REQ-F1-003: The framework shall define default restart, quarantine, and escalation policy per app class.
- REQ-F1-004: Default hosted interactive workloads shall use less than `10 GB` memory unless a heavier workload class is explicitly selected.
- REQ-F1-005: Default hosted interactive workloads shall use half of available system threads unless a heavier workload class is explicitly selected.
- REQ-F1-006: Compiler, test runner, and similarly heavy batch workloads may opt into larger memory and thread budgets than the default hosted profile.
- REQ-F1-007: Kernel or bare-metal invariant violations shall escalate to halt or reboot semantics rather than attempting normal hosted-app restart semantics.
- REQ-F1-008: Dashboard framework worker launch shall propagate the selected runtime budget into the child process environment so inner watchdog logic and outer shell limits agree.
- REQ-F1-009: Repeated worker crashes inside the restart window shall transition the workload into quarantine rather than restart indefinitely.
