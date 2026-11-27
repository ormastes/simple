# Caret distributed orchestrator NFRs

Preserved selected-plan source SHA-256:
`405d7a5ba1c5b5d149eea1fe8c7a196d93d00dd17c07882b57f886a7b46aa368`.
The main-worktree original remains unchanged. Historical slice descriptions below
are not current measured evidence. Current status: **AWAITING_VERIFICATION**;
see `doc/03_plan/sys_test/orchestrator_verification_wait_20261107.md`.
The later explicitly agreed execute packet bounds are 2 MiB outer framing and
1 MiB retained request, measured in bytes. Those codec limits do not qualify
runtime stream/replay bounds or change the proposed stream budgets below.

Selected by the user's 2026-11-06 revision-1 plan.

- Ownership: one writer per domain; no second daemon/journal framework, global
  prune, PID-only adoption, or competing terminal reader.
- Resource admission: hard minima, physical-host accounting, checked arithmetic,
  and retained charges for uncertain work. Never inherit fiber overcommit policy.
- Recovery: immutable operations and fences; unknown outcomes do not authorize
  replay or free capacity. Cancellation acknowledgement is not reaping evidence.
- Security: typed argv, approved mounts/secrets, authenticated grants, private
  engine endpoints; schema validation alone is not authorization.
- Protocol bounds: proposed decoded frame budget 1 MiB, stream chunk 64 KiB,
  replay budget 8 MiB; qualify implementation independently before advertising.
- Performance: record baseline startup/latency/RSS and local build/test behavior
  on designated fixtures before setting numerical release budgets.

The resource-set slice caps input text length at 1,048,576, total resource
envelopes at 1,024 (including lists), and resource-list depth at 16 below the
root. It iteratively walks values and uses an identity dictionary. These are
loader limits, not proof of bounded parser recursion or authenticated transport
safety. Canonical parser pre-parse structural limits remain a remote-input gate.

Verification: limit/overflow scenarios in the resource-set spec; required
compiler/lib/MCP checks and runtime provenance gates. No performance or runtime
qualification measurements have been produced by this change.
