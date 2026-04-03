<!-- codex-design -->
# Architecture: Crash Containment Framework Bare-Metal Simplified

**Date:** 2026-04-03
**Feature:** `crash_containment_framework`

## Goal

Define the shortest correct bare-metal version of the crash-containment model.
Hosted apps can use restart and quarantine. Bare-metal should not.

## Simplified Rule

On bare metal:

- expected failures return `Result<T, E>`
- invariant failure triggers panic/trap/abort
- panic does not resume execution
- watchdog handles hangs
- reset policy decides reboot or halt

## Bare-Metal Domains

### Trusted Running State

Allowed:

- normal control flow
- `Result<T, E>` returns
- bounded retry for recoverable device/transport failures

Not allowed:

- continuing after corrupted state
- restarting application logic inside the same poisoned runtime context

### Panic State

Triggered by:

- invariant violation
- impossible branch
- corrupted memory or state
- unimplemented required path in production
- explicit abort path

Response:

1. record minimal diagnostics if still safe
2. stop normal execution
3. transfer to halt or reboot policy

### Hang State

Triggered by:

- deadlock
- infinite loop
- scheduler stall
- runtime lockup

Response:

- local watchdog timeout
- hardware or external watchdog reset if the runtime stops making progress

## Policy

### Panic

- default disposition: `reboot`
- use `halt` only where reboot is unsafe or would hide debug evidence

### Trap / Abort

- treat as fatal
- do not retry in the same execution context

### Watchdog Timeout

- treat as stronger evidence than a normal panic
- assume scheduler/runtime may be wedged
- rely on watchdog reset path, not software recovery

## What Bare-Metal Should Not Copy From Hosted Apps

- repeated child restart loops
- quarantine timers
- session-level restart windows
- “resume in place” after panic
- large dynamic supervision trees

Those make sense for hosted user-space workloads. They are the wrong default for
bare-metal domains.

## Minimal Implementation Shape

- panic handler:
  - capture reason
  - emit minimal diagnostics if possible
  - halt or request reset
- watchdog:
  - fed only from healthy scheduler or main-loop progress points
  - if not fed, reset the board/system
- boot path:
  - record reset reason when hardware supports it
  - classify panic-reset vs watchdog-reset

## Recommended Defaults

- threads: `1`
- hosted-style memory caps: not applicable as primary policy
- restart budget: `0`
- disposition on invariant failure: `reboot`
- disposition on unrecoverable kernel corruption: `halt` or board-specific reset

## Relationship To Main Framework

The main framework doc defines the full hosted-platform model.
This simplified bare-metal model is the reduction of that policy for domains
where:

- state corruption is more dangerous
- supervision is shallower
- watchdog/reset is the real recovery path

See the main architecture doc:

- [`doc/04_architecture/crash_containment_framework.md`](/home/ormastes/dev/pub/simple/doc/04_architecture/crash_containment_framework.md)
