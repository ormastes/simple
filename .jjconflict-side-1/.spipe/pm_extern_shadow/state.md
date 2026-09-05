# pm_extern_shadow — lane PMSVC

Status: **DONE** (2026-07-27). All 6 describe blocks 0 failures, both engines.

## Problem

`src/os/services/pm_service.spl` declared four `extern fn`s
(`loader_exec`, `signal_deliver`, `signal_queue_has_pending`, `vmm_cow_clone`).
The in-file extern declarations beat the spec's same-named test stubs, so
`pm_exec` / `pm_exit` / `pm_kill` called dangling in-guest-only symbols on the
host. On the host they silently returned 0/garbage instead of aborting, so the
spec's stub counters never moved.

Three red examples (one per red block):

| block | example | symptom |
|---|---|---|
| exec | `pm_exec on valid pid calls loader and returns 0` | `test_loader_exec_calls` 0, expected 1 — stub never ran, extern returned 0 |
| exit and waitpid | `pm_exit notifies parent via signal_deliver(SIGCHLD)` | `last_signo` 0, expected 17 |
| kill and find | `pm_kill on valid pid returns 0 and invokes signal_deliver` | `last_signo` 0, expected 9 |

All three are the same extern-shadow class. `vmm_cow_clone` was the same defect
but latent — fork tests never asserted on the cloned vmspace, so a garbage
return went unnoticed.

## Fix — port/outbox model (mirrors the TERM change in `tty_service.spl`)

`pm_service.spl` now declares **no** `extern fn`. Each kernel-side effect is
recorded as an intent in an in-module outbox with a drain accessor; the
kernel-side consumer (which declares its own externs — `kill.spl`,
`loader_api.spl`, `vmm_vma.spl` already do) drains, performs the real effect,
and reports back:

| effect | record site | drain | report back |
|---|---|---|---|
| signal | `pm_exit`, `pm_kill` | `pm_take_pending_signal()` | — (fire and forget) |
| exec | `pm_exec` | `pm_take_pending_exec()` | `pm_exec_complete(pid, path, entry)` |
| vmclone | `pm_fork` | `pm_take_pending_vm_clone()` | `pm_bind_vmspace(pid, pml4, id)` |

New types: `SignalIntent`, `ExecRequest`, `VmCloneRequest`.
New accessors: `pm_signal_count`, `pm_last_signal_pid`, `pm_last_signal_signo`,
`pm_exec_request_count`, `pm_vm_clone_request_count`, and on `PmWorld`
`exec_image_for_entity`, `pending_mask_for_entity`.

Contract change: `pm_exec` now returns 0 = *accepted* (or `-ESRCH`); the loader
errno is propagated by `pm_exec_complete`. `pm_fork` leaves the child's
`VmSpaceRef.pml4 = 0` (unbound) until `pm_bind_vmspace` lands. No in-tree
consumer of `PmService` exists yet (`src/os/services/mod.spl` only re-exports),
so nothing else needed updating.

Externs removed: `loader_exec`, `signal_deliver`, `vmm_cow_clone`, and
`signal_queue_has_pending` (that one had no caller at all).

## Verification

- `bin/simple run test/01_unit/os/services/pm_service/pm_service_spec.spl` —
  6 blocks, 25 examples, **0 failures** (was 20 examples / 3 failures).
  Identical under `SIMPLE_EXECUTION_MODE=interpreter`.
- Neighbours unchanged and green: `sched_service_spec.spl` (4 blocks),
  `ds_service_spec.spl` (7 blocks) — 0 failures each.
- **Non-vacuity negative controls** (mutate source, confirm the spec catches it,
  revert): deleting the `if entry < 0` guard in `pm_exec_complete` fails
  *"propagates loader failure"*; retargeting the SIGCHLD intent from
  `parent_pid` to `pid` fails *"records a SIGCHLD notification aimed at the
  parent"*. Both reverted.
- `bin/simple lint src/os/services/pm_service.spl` emits
  `semantic: method 'get' not found on type 'str' (receiver value: PmWorld)` —
  **pre-existing**, byte-identical on `git show HEAD:` of the same file. Not a
  regression from this lane; not investigated further (out of scope).

## Open / handed on

- Stale duplicate tree `test/unit/os/services/pm_service/pm_service_spec.spl`
  (legacy path, last touched by `37cda4befdc` "restore main from pushed jj
  conflict tree") still carries the old extern-stub spec and the pre-change
  `pm_exec` contract. It was already failing before this lane; it is outside
  lane PMSVC's owned paths. Whoever owns the `test/unit/` -> `test/01_unit/`
  migration should delete it or port it. Resume: it is a byte-level ancestor of
  the `01_unit` spec, so `git rm` is the likely correct action.
- The kernel-side glue that drains these outboxes is not written yet — PM is
  currently the only side of the port. That is unchanged from before (PM had no
  consumer then either), but the drain API now makes the missing half explicit.
