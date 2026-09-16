# `rt(hal)` clock sealed-result binding gap

## Current bounded production slice

`time_now_nanos()` now calls the canonical Pure Simple leaf
`hal_clock_monotonic_nanos_v1()`. The hosted binding is a direct call to the
existing scalar runtime provider. It preserves the public result/error contract
and is O(1), one provider call, zero collections, zero lookup, and zero dynamic
allocation.

## Remaining blocker to alpha/beta clock comparison

The sealed provider protocol cannot currently return the captured clock value:

- `HALRES1` exposes normalized/trace digests and lengths, but no caller-owned
  result payload or scalar observation field.
- provider workers hash the request fixture; they do not consume an
  `EnvOpcodeV1.ClockRead` observation.
- the only physical clock executor is under `src/app/test/`, so importing it
  from `src/lib/nogc_sync_mut/io` would invert the production layer boundary.
- there is no init-owned process-global/session binding that a tagged library
  operation can use without environment lookup or hot allocation.

Routing the public clock through the present sealed invocation would therefore
replace a real timestamp with a digest, or require a second raw clock read after
comparison. Either changes semantics or compares a different observation.

## Required patch prerequisite

1. Add a fixed caller-owned result region `(offset, length, capacity)` to the
   frozen request/result ABI and sealed session; no pointer crosses a process.
2. Add a production parent-owned `ClockRead` capture owner below `src/app/test`.
   It performs exactly one physical read, writes one fixed observation, and
   replays that same observation to all shadow providers.
3. Generate a closed operation-id-to-direct-binding table from `@rt(hal)`
   manifests during compilation. Unknown or mismatched bindings fail closed;
   no reflection, environment lookup, or text parsing occurs after init.
4. Prepare and seal the coordinator before critical entry, then publish an
   immutable generation handle. Invocation uses fixed buffers and reports zero
   post-seal allocation/spawn counts.
5. Prove normal mode returns the preferred captured scalar, alpha/beta compare
   the identical captured observation, and negative provider status retains
   `E-SFFI-TIME-002` behavior.

Acceptance evidence must include same-fixture direct-versus-dispatch timing,
peak RSS, post-seal allocation/spawn counters, and a sabotage test that changes
one replayed observation and forces divergence.

## Compiler binding prerequisite (2026-08-22 follow-up)

The HIR contract pass now resolves the canonical manifest through the closed
`rt_hal_static_binding_v1` table.  The clock row binds the existing direct leaf
and sealed V2 scalar entry point and rejects any signature other than
`fn() -> i64`.  `io.environment.get.v1` binds its normal direct leaf, but a
multi-provider declaration fails closed with `E-RT-HAL-BIND-003` because the
sealed ABI still has no bounded text result.  Unknown operation identities also
fail closed; there is no reflective or environment-based fallback.

This is intentionally a compiler validation/binding prerequisite, not a fake
call rewrite.  Replacing a call to `time_now_nanos()` with the raw scalar leaf
would bypass its negative-sentinel panic and change the public error contract.
The compiler also has no immutable per-entry run-mode input at call lowering,
so it cannot safely select normal versus alpha/beta there.  The remaining
implementation must generate a same-signature wrapper after the mode owner and
bounded result ABI are available, then attach that wrapper to resolved calls.

Compile-time cost is O(manifest bytes) once per tagged declaration (bounded by
2,048 bytes) plus O(1) closed-row selection and signature validation.  Runtime
cost, allocation count, and dispatch overhead remain exactly unchanged because
the new checks emit no hot-path instruction, collection, copy, or lookup.
