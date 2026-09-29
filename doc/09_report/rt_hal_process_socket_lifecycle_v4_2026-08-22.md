# rt(hal) process/socket lifecycle V4 evidence

Date: 2026-08-22

The production process-wait and socket-connect leaves retain the frozen
14-argument buffer ABI, but every compiler mode now enters one init-owned
native lifecycle authority. Calls before initialization or without a trusted
preparation receipt fail before provider dispatch. Generation is supplied by
the trusted process/socket preparation owner; it is never inferred from a
fixture, cursor, or hash. The exported preparation facade is `@unsafe(ffi)` and
is therefore a composition boundary, not an untrusted application API.

The owner uses at most 256 static slots with one lock per slot. Slot selection
is O(1). Different fixture IDs that collide modulo the configured capacity are
rejected without eviction; operators must size the fixed table for their known
fixture set. There is no probing, growing collection, heap allocation, retained
caller pointer, process spawn, socket operation, or environment read in the
authority. Provider output is staged in a 32-byte stack scratch region and is
copied to caller storage only after the matching receipt finishes successfully.
A failed dispatch/finish poisons the registered generation permanently; only a
strictly newer explicit registration can replace it.

Focused command:

```sh
sh scripts/check/check-hal-process-socket-lifecycle-v4.shs
```

Measured on this Linux host at source revision `8199a99b77ca` plus the working
V4 tranche (`cc -std=c11 -O2`, 100,000 register+direct-dispatch operations):

- 86 ns per registration plus dispatch
- peak RSS: 1,792 KiB before and after
- hot allocation count: 0
- same-slot concurrent admission: exactly one
- distinct-slot concurrent dispatch: both complete
- result: `STATUS: PASS`

The prior pre-scratch development row was 39 ns per registration plus dispatch.
The retained 47 ns safety cost stages at most 32 bytes so failed finish cannot
expose provider output. This is constant-size work and does not change the
public ABI.
