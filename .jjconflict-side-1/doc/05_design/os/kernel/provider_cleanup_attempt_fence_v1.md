# Provider cleanup attempt fence v1

Status: implemented as an unwired prerequisite; unverified.

## Scope

`provider_cleanup_attempt_fence_v1.spl` supplies one bounded, mutex-serialized
owner for provider-side cleanup attempts. It does not publish scheduler states,
authorize `Zombie`, invoke an FD/grant/database provider, or claim QEMU/runtime
evidence.

The canonical mutable state is the module singleton. Boundary values are
opaque handles: provider authority, attempt, side-effect start identity, cancellation
request, cancellation acknowledgment, and completion receipt. They are copied
identities, not independent mutable owners. Every mutation revalidates the
complete slot generation, nonce, provider identity, cleanup transaction, and
attempt ordinal against the singleton.

## Lifecycle

```text
Free --provider issue--> Issued --provider start--> Started
  Issued/Started --cancel request--> CancelRequested
  Started/CancelRequested --provider complete--> Completed --finish--> Free
  CancelRequested --provider quiescence ACK--> Cancelled
  Cancelled --same provider retry--> Issued(next generation + ordinal)
```

Cancellation request is deliberately non-authorizing. The registered provider
must attest quiescence with bounded evidence. Retry validates that exact ACK and
rotates generation, nonce, and ordinal atomically. An old copied side-effect
permit therefore cannot complete after retry. If completion wins the race while
cancellation is pending, completion becomes terminal and the later cancellation
ACK is rejected; callers must consume the completion rather than dispatch a
retry.

Exact repeated completion and cancellation ACK are idempotent. Conflicting
duplicates fail closed. Nonzero, non-wrapping identities prevent ABA; exhausted
slots retire. The owner is bounded to 16 providers and 128 live attempts, and
all retained evidence strings are capped at 128 bytes. Transaction overlap
checks are bounded O(128) linear scans with no work-proportional allocation;
handle validation is direct-index O(1).

## Ownership and integration contract

The provider owns actual side effects and is the only domain allowed to call
start, complete, acknowledge cancellation, and issue retry using its opaque
authority. Start is accepted once only. Its returned copied value is a
completion identity plus a non-authorizing target view; it is not a transferable
execution permit and cannot prove unique dispatch by itself. Each integrating
provider must retain the authority inside one attempt-ID dispatch/dedup owner,
and may schedule real work only for the single successful start transition.
The future scheduler adapter may request cancellation and observe receipts, but
a timeout is never a quiescence proof. Attempt handles do not survive fork.
Side-effect start returns an immutable target view containing the
owner-recorded task, lifecycle, transaction, generation, and attempt ordinal;
the view carries no authority, but prevents adapters from substituting
caller-provided cleanup targets. A terminal cancellation ACK can either be
consumed into a retry or explicitly finished to release its bounded slot.

Before scheduler wiring, each FD, grant, and DBD adapter must retain its own
authority and bind its provider result to the immutable task ID, lifecycle
generation, transaction ID, and transaction generation represented by the
attempt slot. Scheduler exit/reap must then retain the transaction until every
required provider has either completed or produced a separately authenticated
quarantine disposition. This module alone does not satisfy those requirements.

## Static coverage

`test/01_unit/os/kernel/scheduler/provider_cleanup_attempt_fence_v1_spec.spl`
covers one-shot start, exact completion replay, conflicting completion, provider separation,
cancellation-before-retry, old work completing after cancellation, completion
winning the race, duplicate transaction rejection, and fork rejection.
