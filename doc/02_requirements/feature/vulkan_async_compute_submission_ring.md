# Vulkan async compute submission ring

**Status:** selected for implementation
**Selection:** Option B — runtime-owned bounded submission session
**Compatible NFR:** N2 — tunable bounded ring with pressure policy
**Evidence date:** 2026-09-09

The runtime owns the submission session, slot capacity, command/resource
retention, completion polling, and exact retirement. Simple receives copied
generation-bound receipts and owns renderer policy only. Version one admits at
most one direct-compute session per device generation; legacy global compute
operations reject while that session is active.

## Functional requirements

- **REQ-VKASYNC-001 — session lease:** Create a generation-bound session with
  capacity selected at construction from 3 through 16. Capacity never grows
  implicitly. The session binds device identity, queue family, owner, and slot
  generations atomically.
- **REQ-VKASYNC-002 — bounded lifecycle:** A slot follows
  `Free(g) -> Recording(g) -> Submitted(g) ->
  CompletedAwaitingRetirement(g) -> Free(g+1)`. Capacity counts every live
  recording, submitted, and completed-awaiting-retirement slot.
- **REQ-VKASYNC-003 — exact retirement:** Polling proves the exact fence or
  timeline completion without a device-wide wait, then frees command storage
  and releases every retained owner exactly once. A stale receipt cannot act on
  a reused slot. Physical resources remain alive while a presenter/capture
  receipt still reads them.
- **REQ-VKASYNC-004 — pressure:** When full, poll the oldest slot once. The
  configured policy may perform at most one bounded wait for that slot or
  return `would-block`; no busy-spin, implicit growth, sleep loop, or hidden
  `wait_idle` is allowed.
- **REQ-VKASYNC-005 — cancellation and loss:** Cancellation closes admission
  but never claims GPU preemption. Accepted work drains after proof of
  completion. Unknown completion/device loss fail-stops the session and retains
  all owners until explicit recovery or teardown resolves them.
- **REQ-VKASYNC-006 — ordering:** Submission sequence is monotonic. Physical
  retirement may be out of order, while frame-visible receipts publish only the
  contiguous sequence prefix.
- **REQ-VKASYNC-007 — concurrency:** A bounded wait never holds the global
  runtime registry mutex. A generation-pinned per-slot lease permits another
  slot to poll counters or progress while one slot waits.
- **REQ-VKASYNC-008 — lifecycle safety:** Handle/session/slot allocation fails
  closed before zero, collision, or wraparound. Destroying a live pending
  submission cannot orphan its only owner token; it must reject or perform
  signaled-only exact retirement. Close is idempotent.

## Traceability

| Requirement | Parent requirement | Planned evidence |
|---|---|---|
| REQ-VKASYNC-001 | REQ-GPUUI-004, 005 | capacity 3/8/16 live-device matrix |
| REQ-VKASYNC-002 | REQ-GPUUI-004 | slot state and reuse test |
| REQ-VKASYNC-003 | REQ-GPUUI-003, 004 | owner-retirement and stale-token test |
| REQ-VKASYNC-004 | REQ-GPUUI-005 | ring-full/backpressure evidence |
| REQ-VKASYNC-005 | REQ-GPUUI-003, 004, 005 | cancellation/device-loss matrix |
| REQ-VKASYNC-006 | REQ-GPUUI-004, 005 | contiguous publication test |
| REQ-VKASYNC-007 | REQ-GPUUI-005 | two-thread mutex-contention test |
| REQ-VKASYNC-008 | REQ-GPUUI-003, 004, 008 | stale/wrap/close negative tests |

## Compatibility

Option A + N2 and all blocking-only implementations are rejected for this
feature. N1 remains a diagnostic fixed-three-slot comparison row, not the
selected production contract.
