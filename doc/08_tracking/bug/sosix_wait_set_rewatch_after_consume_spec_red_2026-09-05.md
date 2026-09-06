# `completion_wait_set_spec` red: re-watching a consumed generation accepts a duplicate notify

Filed 2026-09-05. Status: CLOSED 2026-09-05. Pre-existing (reproduced BEFORE and AFTER the
`os.sosix.core -> std.common.contracts.sosix` lift). Fixed in
`src/lib/common/contracts/sosix/wait_v1.spl`: `SosixWaitSet` keeps a bounded
`consumed` list (evicts oldest at `SOSIX_WAIT_SET_MAX_OPERATIONS`) recorded by
`take_ready`/`take_ready_for`; `notify` rejects a consumed generation even after a
re-watch. `completion_wait_set_spec` 4/5 -> 5/5, `fs_sync_spec` still 4/4.

## Symptom

`bin/simple test test/01_unit/os/sosix/completion_wait_set_spec.spl --no-session-daemon`
-> `Results: 5 total, 4 passed, 1 failed`; failing example
`publishes one consumable notification for a watched generation`
(`test/01_unit/os/sosix/completion_wait_set_spec.spl:62-78`), `expected true to equal false`.

## Cause

`SosixWaitSet.notify` (`src/lib/common/contracts/sosix/wait_v1.spl`, formerly
`src/os/sosix/core/wait_set.spl:44-62`) removes the watch on notify so a duplicated
transport completion cannot wake the consumer twice — but after `take_ready`
the spec re-installs the watch (`:77`) and expects a second `notify` of the same
generation to be rejected (`:78`). The implementation has no memory of consumed
generations, so it accepts it. The spec documents the intended one-shot-per-
generation contract; the implementation is weaker.

## Unblock

Decide the contract in plan task B3 (the first hosted consumer of `wait_v1`):
either track consumed generations in a bounded set (must stay allocation-free
after creation) or reject `watch` of a generation that was already consumed.
Then the spec goes green without edits. Evidence: `bin/simple` is the Rust seed
(`bin/release/aarch64-unknown-linux-gnu/simple`, 2026-09-04 14:46).
