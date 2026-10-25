# C4 prepaid cleanup integration boundary v1

Status: exact native source 73d4ee09fd7 received conditional UNSAFE/private
SOURCE_GO; one root-authorized new cleanup regression passed ASan/UBSan. Safe
compiler pin/account admission remains UNRUN and the safe facade stays disabled.
The merged native primitive's six-attempt budget remains exhausted. This is a
new request-lifetime integration obligation, not a retry of those green checks.

## Problem and retained owners

Current close, read-end and release observe a mutable global lookup bound and
reserve on the shared account at cleanup time. A producer can close/exhaust that
account; unrelated allocations can increase the lookup bound after an earlier
reservation. Therefore saving today's close bound is insufficient.

The request retains its typed context, original producer error and separate
cleanup error until actual native release succeeds. A compiler-private affine
context owns one native control pin from birth to release; short read leases
borrow that pin. No admitted call can raw-free the control, copy/reconstruct the
context's lifetime state, or use a consumed context. Direct live-pointer
operations below are conditional on this compiler provenance/lifetime proof.
They are not general token observers, and generation comparison alone cannot
make dereferencing an arbitrary or freed pointer safe.

## Proposed private scalar ABI

| Export | Arguments | Result |
|---|---|---|
| rt_source_region_live_cleanup_bound_v1 | operation, metric | fixed bound, no lookup/lock/account access |
| rt_source_region_revoke_live_v1 | live_control, generation, prepaid_work | 0 or fixed scalar error |
| rt_source_region_read_end_live_v1 | live_control, generation, lease, prepaid_work | 0 or fixed scalar error |
| rt_source_region_release_live_v1 | live_control, generation, prepaid_work | 0 or fixed scalar error |

Cleanup operations: 1 revoke, 2 read-end, 3 release. Metrics retain 0 work,
1 state fields, 2 allocation bytes. Operations allocate nothing; fields/bytes
are zero. Fixed logical work is revoke=16, read-end=24, release=64. These constants
cover direct header accesses and, for release,
one existing-owner trylock, exact backlink validation/removal, and fixed-size
control/metadata reclamation. No call loops, waits, scans or derives its charge
from global registry size. Bound-query work itself is prepaid before producer.
The existing scalar error vocabulary and other primitive signatures remain.

## Existing-owner representation refinement

Ordinary extent entries stay exactly two native words. Member SOURCE metadata
stays unchanged. Only control metadata adds a registry-slot backlink, and the
control record retains its immutable control-metadata pointer. These extra
control-only fields/bytes are included in the existing create metrics.

Control metadata is 48 bytes (unchanged 40-byte member prefix plus backlink);
the control adds one immutable metadata pointer. Create metrics include 18
fields and both actual control/metadata extents. Member metadata stays 40 bytes.

The existing insertion/rehash loop already knows its destination slot. It updates
a SOURCE control's backlink while copying that entry, with a high-bit/control
check; no second lookup, new registry, ordinary allocation metadata, or global
walk is added. An unrelated resize can change the backlink without invalidating
the pinned control or changing the fixed cleanup charge.

Release acquires the existing owner lock without waiting, then checks slot in
range, exact entry pointer, exact decoded metadata pointer, control kind, extent,
generation and execution owner. It also requires revoked state, zero members and
zero active leases. It can consume an already-revoked pending writer under that
lock. Only then does it remove the entry, retire metadata and free the control.
A mismatch/contention/conflict retains the live owner and returns an explicit
cleanup error. Registry revision exhaustion cannot prevent retirement.

## Revocation and concurrency proof obligations

Closed becomes an atomic flag at every existing read/write/retirement access.
Live revoke checks prepaid work and immutable generation/TLS identity, then only
atomically stores closed. It does not clear plain ticket/member fields without
the owner lock. Revoked tickets cannot commit because every commit checks closed
under its existing lock before the store.

Live read-end checks the pinned immutable identity and exact outstanding lease,
then consumes the owner-thread lease once. It needs no registry lookup or account
access. A lockless implementation additionally requires the already-selected
single mutable execution owner: no foreign operation may write lease state;
foreign retirement touches only atomic closed and lock-protected membership.
This candidate selects the single-owner lockless path; it remains UNSAFE/private
until the actual affine pin-verifier receipt establishes that precondition. No cross-thread borrowed-load/free safety is claimed
until compiler confinement is established independently.

## Facade escrow and failure transport

Before invoking a producer, reserve distinct revoke and release-attempt credits
on the same shared account. Before each successful read-begin, reserve its native
begin work and a distinct fixed end credit, with no fallible reservation after
the native lease is created. Every attempted native cleanup consumes its credit
once, including failed trylock/conflict attempts. Do not re-use one credit for
unbounded retries or reserve against an already-closed account.

Context state must record live/released ownership, pending lease/end credit,
pending ticket/commit credit, and each unused cleanup credit. Request state
retains the first producer error and independent cleanup error. A failed release
does not clear the live token or report released. A later retry needs separately
prepaid transport credit; without it, return explicit capacity/cleanup failure
while retaining the owner. No unconditional eventual-free guarantee under
permanent contention is claimed and no retry count/policy cap is invented.

The context invalidates its live capability on successful release and rejects
all subsequent direct-pointer operations before entering native code. Producers
cannot construct, overwrite, share or consume this compiler-private lifetime
state. Pending leases/tickets must unwind before final release; revocation alone
does not pretend their rich storage is reclaimed.

## Review and execution separation

Native owner changes belong to the cleanup integration lane; facade/request
changes belong to the HIR/account lane. Root is merge owner; independent review
must approve this boundary and the exact source delta. The original primitive
test binary is not re-run. Any future new cleanup-specific execution requires
explicit root scheduling and records its separate obligations: account closed
or exhausted, unrelated owner rehash, pending read lease end, one-use credits,
retained original/cleanup errors, contention, and no stale live capability.

No whole SOURCE, container, pure/hosted or compiler-confinement admission
follows from the conditional source review and private native execution.

Owned files are runtime_memory.c, runtime_source_region_v1.h/.inc and the
new runtime_source_region_cleanup_credit_v1_test.c. No safe facade integration
is enabled. The new fixture uses genuinely born retained C controls and checks
fixed credits after actual unrelated registry rehash, lock-independent revoke/
lease end, retained owner on trylock/lease/member conflicts and explicit distinct
attempt credits. It supplies neither an executed shared-Simple-account nor compiler pin
receipt and never calls the exhausted general primitive test.

## Exact private native evidence (2026-10-25)

Production and fixture revision: `73d4ee09fd7`. Independent reviewer found no
P0/P1 under the explicitly UNSAFE genuine retained-pin/single-owner contract.
Root authorized one new cleanup-specific compile/run; that attempt passed:

```sh
cc -std=gnu11 -O0 -g -fsanitize=address,undefined -ffunction-sections -fdata-sections -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -pthread test/01_unit/runtime/runtime_source_region_cleanup_credit_v1_test.c src/runtime/runtime_native.c -Wl,--gc-sections -ldl -lm -o /tmp/simple-c4-cleanup-native-test
/tmp/simple-c4-cleanup-native-test
```

Exit 0: `C4 private live cleanup integration: PASS (safe pin/account admission UNRUN)`.
No sanitizer findings. Observed peak RSS was 238596 KiB for compilation and
10504 KiB for execution, below the authorized 1 GiB bound. Private timing/RSS
receipts: `/tmp/c4-cleanup-native-compile.time` and
`/tmp/c4-cleanup-native-run.time`.

The fixture executed actual native transient scope ownership, unrelated ordinary
registry growth/rehash before cleanup, live revoke/read-end while the existing
owner lock was held, retained control after failed trylock/lease/member checks,
distinct attempt allowances, and retirement of a revoked writer after its member
was freed. It did not re-run the exhausted general primitive test. New cleanup
attempt count is one; no repeat is needed. The earlier six-attempt primitive
budget remains exhausted. This is not an actual Simple account-close/exhaustion,
affine verifier receipt, safe facade admission, performance qualification or
whole SOURCE acceptance.
