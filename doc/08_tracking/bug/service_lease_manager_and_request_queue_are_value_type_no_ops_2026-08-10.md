## RESOLVED — re-verified 2026-08-17 (STALE, close)

Both halves are fixed in the tree.

* `LeaseManager` is now `class LeaseManager` (`lease_manager.spl:77`) with `me`
  methods; the free `fn`s at :197-213 are thin delegates. The file header
  documents the struct->class rationale.
* `RequestQueue` no longer exists — module deleted as dead code in
  `5f4b65fe885b` ("refactor(service): delete the dead RequestQueue module");
  `grep -rl RequestQueue src/ test/` returns nothing.

Direct `bin/simple run` repro over the free-function API (every row from the
defect table above):
```
r1.ok=true id=lease-1
r2.ok=false            <- second exclusive acquire is BUSY (was ok:true)
count=1 excl=true      <- active_lease_count/has_active_exclusive (were 0/false)
released=true          <- release_lease finds the lease (was always false)
count_after=0
```

# `std.service` LeaseManager and RequestQueue are total no-ops (struct value semantics)

- **Status:** OPEN (RED)
- **Filed:** 2026-08-10
- **Severity:** HIGH — the `sj` daemon's mutation serialization does not serialize anything.
- **Found by:** rewriting three specs that had been testing their own private
  re-implementation instead of `src/` (stream P2).

## Summary

`src/lib/nogc_sync_mut/service/lease_manager.spl` and
`src/lib/nogc_sync_mut/service/request_queue.spl` declare their state holders as
`struct` — a **value** type in Simple:

- `struct LeaseManager` (lease_manager.spl:38)
- `struct RequestQueue` (request_queue.spl:17)

Every mutating operation is a free function taking that struct **by value**:
`try_acquire_exclusive`, `try_acquire_shared`, `release_lease`,
`_reclaim_ghosts`, `_next_lease_id`, `enqueue`, `dequeue`, `queue_drain`,
`_next_queue_id`. Each mutates its own copy; the caller's value is unchanged.

Observable consequences (measured, not inferred):

| Product claim | Actual behaviour |
|---|---|
| second exclusive acquire returns BUSY | returns `ok: true` — **unlimited concurrent exclusive leases** |
| `active_lease_count` after a grant | always `0` |
| `has_active_exclusive` after a grant | always `false` |
| `release_lease(id)` | always `false` (never finds the lease) |
| lease ids unique | always `lease-1` |
| `queue_len` after enqueue | always `0`; `queue_is_empty` always `true` |
| `dequeue` FIFO | never advances; ids always `req-1` |
| `queue_drain` | returns `[]` regardless of enqueues |

This propagates to `src/app/sj_daemon/request_handler.spl:62-73`: the BUSY /
exit-75 path is **unreachable**, so the daemon can never refuse a concurrent
mutating command.

## Why it was invisible

`lease_grant_spec`, `request_queue_spec` and `busy_contract_spec` each declared
their *own* `struct LeaseManager` / `RequestQueue` inside the spec file and
reimplemented the logic. They never imported `std.service.*`, so they were green
(or failing for spec-local reasons) while the product was completely broken.

## Also: a spec-invented API

`busy_contract_spec` asserted against a `format_busy_json(lease_id, holder_pid,
expires_at)` function. **No such function exists anywhere in `src/`.** The real
BUSY wire format is `response_json(CommandResponse)`
(`src/app/sj_daemon/request_handler.spl:47`) carrying `exit_code: 75` and the
lease's `busy_message` in `stderr`. The spec has been rewritten against the real
one; `response_json` itself works (verified — it renders `"exit_code":75` and
`"classification":"mutating"` correctly), only the empty `busy_message` fails.

## Current verdicts (after rewrite, product unchanged)

```
SPEC FILE VERDICT: test/01_unit/lib/service/lease_grant_spec.spl   declared>=13 executed=13 passed=4  failed=9 dropped=0
SPEC FILE VERDICT: test/01_unit/lib/service/request_queue_spec.spl declared>=9  executed=9  passed=2  failed=7 dropped=0
SPEC FILE VERDICT: test/01_unit/app/sj/busy_contract_spec.spl      declared>=7  executed=7  passed=1  failed=6 dropped=0
```

The 22 failures are all one root cause. They are left RED deliberately.

## Unblock condition

Convert `LeaseManager` and `RequestQueue` from `struct` to `class` (reference
semantics), or restructure the mutating free functions to return the updated
value and have every caller rebind. `class` is the smaller change and matches
the intent of the module docstrings. Callers to update on the `class` route:
`src/lib/nogc_sync_mut/service/daemon_base.spl`,
`src/app/sj_daemon/request_handler.spl`,
`src/lib/gc_async_mut/service/lease_manager.spl` (re-export).

Related: `doc/08_tracking/bug/spec_value_type_helper_mutates_copy_family_2026-08-10.md`
(the spec-local instance of the same value-type trap).
