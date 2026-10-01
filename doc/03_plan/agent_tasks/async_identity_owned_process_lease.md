# Async identity-owned process lease — agent tasks

## Fixed interfaces

All lanes target the API names in
`doc/05_design/runtime/async_identity_owned_process_lease.md`. No lane may add
a raw PID cancellation path, expose token words, implement a second registry,
or weaken unsupported-platform refusal.

Manual-facing scenario steps, if SPipe is added, are fixed as:

1. `step("start an identity-owned process lease")`
2. `step("poll bounded output while the process remains live")`
3. `step("request cancellation through the owning capability")`
4. `step("observe TERM, grace, KILL, and exact reap")`
5. `step("reject a stale or forged lease")`

Setup/checker helpers are `setup_owned_process_fixture`,
`check_live_lease`, `check_bounded_output`, `check_cancel_sequence`, and
`check_stale_lease_rejected`. Unimplemented helpers must use `assert(false)` or
`fail(...)`.

## Work lanes

| Lane | Owner scope | Deliverable | Dependency |
|---|---|---|---|
| A: runtime core | `runtime_process_owned.c`, `runtime.h` | v2 registry, opaque token, async state machine, v1 composition | none |
| B: ABI bridge | compiler runtime-symbol/SFFI registrations | opaque value ABI with interpreter refusal | A declarations |
| C: Simple facade | `nogc_sync_mut/io/process_ops.spl`, explicit exports | opaque lease and typed receipts/errors | A+B |
| D: C verification | three runtime owned-process selfchecks, MCI wrapper | positive, race, failure-injection, sabotage evidence | A |
| E: Simple/integration verification | facade contract and fake-QEMU integration spec | nonleakage, compatibility, live interaction | B+C |
| F: QemuRunner consumer | later `vm_adapter.spl` change | use lease without new process owner | verified A-E |

Lower-model sidecars: N/A for the runtime ownership and ABI lanes because the
security invariants and shared files require one coherent implementation.
Parallel sidecars may only inventory downstream migration callers after the
highest-capability owner freezes the v2 interfaces.

## Merge and review

- Merge owner: runtime process-capsule maintainer.
- Final reviewer: highest-available capability model, independent of lanes A-C.
- Merge order: A+D, then B+C+E, then F.
- Do not combine unrelated dirty-worktree changes.

## Acceptance gates

- Start returns before a long-running child exits.
- No public surface exposes or reconstructs slot, generation, token, PID, or
  pidfd as authority.
- Forged/stale/collected capabilities fail without affecting a live process.
- Cancel produces one owner-serialized TERM/grace/KILL/reap sequence for the
  complete process group.
- Normal exit and every failure path reap exactly once.
- Output memory and per-poll work remain bounded under an unbounded producer.
- Linux pidfd provider passes; non-Linux/Windows refuse before spawn.
- Existing v1 facade behavior and receipt layout remain compatible.
- MCI process-safety evidence includes the new v2 checks.
- `QemuRunner` integration does not introduce raw `rt_process_*`, shell
  timeout, PID files, or another lifecycle registry.

## Stop conditions

Stop after at most three verify/fix cycles. Any inability to prove entropy,
pidfd identity, group containment, exact reap, opaque-value finalization, or
unsupported-platform refusal is a release HOLD, not a best-effort fallback.
