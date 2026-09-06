# GPU Scheduler Hardening and GPU-Resident Rendering Requirements

## Selected requirements

- **REQ-GPU-SCHED-ASYNC-001:** GPU DrawIR work uses the existing bounded queue and
  canonical terminal-completion model; normal submission does not immediately
  drain/complete the packet.
- **REQ-GPU-SCHED-LIFE-001:** Deferred operations preserve one terminal result and
  reject stale, invalid, full, reset, or duplicate-completion transitions.
- **REQ-GPU-SCHED-PAYLOAD-001:** The production hot path has a registered packed payload
  seam; text SDN remains an explicitly named compatibility/diagnostic path.
- **REQ-GPU-SCHED-PROFILE-001:** A strict GPU-scene profile rejects unsupported semantic
  work rather than silently falling back to CPU execution.
- **REQ-GPU-SCHED-PROOF-001:** GPU residency evidence distinguishes submission,
  execution, retirement, presentation, and display; source contracts do not
  satisfy hardware claims.
- **REQ-GPU-SCHED-SAFE-001:** Invalid, unavailable, or oversized deferred
  routes fail closed before commit.
- **REQ-GPU-SCHED-SAFE-002:** Completion-capacity exhaustion rejects admission
  without hidden drain or unbounded allocation.

## Out of scope for this increment

Complete HTML/CSS/JavaScript GPU execution, a persistent kernel, device-
initiated OS I/O, Metal/D3D12 providers, and universal latency claims require
separate capability-qualified increments.
