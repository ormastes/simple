# HIR worker retirement: selected parent-trackable tools

Selection: user delegated choice (“2. as you want.”); root selected admitted
parent-trackable tools. This supersedes the unchosen kernel/arbitrary-tool
options, which were deleted. Baseline: release309249bd1a0. Implementation and
new runtime tests are pending; no false containment or release PASS.

- REQ-WORKER-001: admit exact executable/configuration profiles whose process
  creation is absent or routed through the surviving parent broker. Unknown,
  stale, or untracked profiles reject before execution. A name or self-declared
  flag alone is not admission evidence.
- REQ-WORKER-002: preserve exact configured executable, argv, environment, cwd,
  target and flags. Do not silently substitute a backend or disable valid
  configured work. Unsupported profile behavior is an explicit admission error.
- REQ-WORKER-003: parent owns every worker and nested tool process lease from
  pre-spawn through frozen receipt/ack. Nested compiler codegen sessions must
  not escape parent ownership when the worker dies.
- REQ-WORKER-004: successful retirement requires the worker and every tracked
  nested owner to have exact terminal/tree-empty/reaped and closure receipts.
  No leader-only or signal-delivered observation permits fallback/publication.
- REQ-WORKER-005: original timeout/crash remains failure after successful
  cleanup. Unknown cleanup, malformed receipt, owner identity mismatch or lost
  acknowledgment blocks replacement, ledger closure and fallback.
- REQ-WORKER-006: one total cleanup deadline at most5000ms, bounded request/log
  bytes and live owner count; no per-child deadline reset or unbounded retries.
- REQ-WORKER-007: actual accepted/rejected tool, nested owner, timeout and
  worker-crash regression tests exercise canonical process ownership and actual
  dispatch. Helpers and source-shape checks alone cannot qualify integration.

Allowed policy is cooperative parent-trackable tools. Arbitrary escaping
children on Darwin, hostile plugins, unregistered raw-spawn paths and tools
that call setsid/setpgid outside the admitted boundary are explicitly outside
this policy. Such tools cannot receive this lane's all_stopped guarantee.
Configured tools become supported only with exact profile evidence and real
positive tests; unknown tools must not be relabelled supported for completion.
