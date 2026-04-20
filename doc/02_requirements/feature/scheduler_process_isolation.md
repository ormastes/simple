<!-- codex-research -->
# Requirements: Scheduler + Process Isolation

## Selected Feature Requirements

- REQ-SPI-001: Kernel tasks must carry explicit scheduler policy metadata: policy, weight, priority, requested slice, fair accounting, deadline budget fields, affinity mask, and home CPU.
- REQ-SPI-002: Kernel tasks must carry explicit process-isolation metadata tied to address-space and capability lifecycle.
- REQ-SPI-003: The scheduler must maintain per-CPU run queues separated by class lanes.
- REQ-SPI-004: The default runnable policy must be fair/background oriented with virtual-deadline selection for fair lanes.
- REQ-SPI-005: `sys_schedule` and `sys_schedctl` must expose scheduler query/control operations through the existing syscall layer.
- REQ-SPI-006: `@task` attributes must parse scheduler policy metadata and validate RT/deadline policies against runtime-family restrictions.

## Deferred

- EDF/CBS deadline admission and runtime replenishment.
- Full RT FIFO/RR starvation/bandwidth guard implementation.
- Hosted sandbox backend changes.
