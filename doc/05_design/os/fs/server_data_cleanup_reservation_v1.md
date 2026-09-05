# Server-data cleanup reservation v1

Status: implemented prerequisite, statically reviewed only, runtime unverified.

## Ownership

The namespace owner remains the sole mutable authority for DBFS namespace
leases. The launch-grant registry remains the sole mutable authority for the
filesystem image grant. The bounded cleanup adapter owns only an opaque joint
reservation row and exact partial-completion receipts; it never authorizes I/O.

Every reservation binds task ID, lifecycle generation, cleanup transaction ID,
transaction generation, and attempt ordinal. Provider handles additionally
bind their private slot generation and nonce. Boundary values are opaque
generation-bound leases, not copied mutable owners.

## Protocol

The global nested-lock order is strictly cleanup adapter → namespace owner →
launch-grant owner. Provider code must never acquire the cleanup-adapter mutex
and may not call back into the coordinator. Future scheduler integration must
preserve this one-way order; reverse acquisition is prohibited.

1. The adapter reserves one of 64 rows before provider mutation.
2. Namespace `Active` becomes `CleanupBound`; authorization accepts only
   `Active`, so copied leases immediately become non-operational.
3. Grant `Redeemed` becomes `CleanupBound` for the same attempt identity.
4. Failure to bind the grant rolls the namespace back to `Active`. If rollback
   cannot be established, the exact namespace reservation remains retained.
5. Commit consumes the namespace reservation first, records that partial
   completion, then consumes the grant reservation. A failed second step
   returns a retryable receipt with the exact identities and never infers
   success from an absent row.
6. Replayed terminal commit returns the retained terminal receipt. Concurrent
   dispatch is fenced by the adapter row. The owner consumes the terminal
   receipt before returning the bounded slot to `Free`; copied acknowledgments
   become stale after the first consumption.

Any mutex-unlock ambiguity after a provider mutation returns an explicit
`Indeterminate` disposition carrying the exact opaque reservation. The adapter
retains it in a non-dispatchable `Indeterminate` row; it is neither terminal nor
retryable and cannot be mistaken for absence or success.

No scheduler exit or `Zombie` transition is wired in this phase. Provider
unlock ambiguity quarantines that canonical owner and therefore suppresses
authority rather than guessing completion.

## Complexity and bounds

Tables are capped at 64 rows. Admission and identity lookup are O(64), with no
unbounded allocation, filesystem scan, payload copy, or dynamic dispatch on
the cleanup path.
