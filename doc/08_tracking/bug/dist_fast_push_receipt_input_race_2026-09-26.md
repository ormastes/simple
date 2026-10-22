# Signed fast-push receipt can race its execution inputs

Status: open. Static review only; the hook files are owned by another active
session, so this lane has not changed them or claimed a runtime result.

`scripts/check/check-pr-fast.shs` checks worktree cleanliness once near line
408 and hashes the binary once near lines 1232–1235. Child checks later open
the binary and source paths near lines 283 and 346; receipt signing occurs
near line 616. A concurrent edit or binary replacement can therefore make
the signed tree/binary identity differ from the bytes actually executed. A
final path rehash alone does not close replacement followed by restoration.

## Required fix

Run checks from an immutable private snapshot that contains every executable
and source input named by the signed receipt. Bind the snapshot tree, binary
digest, checker/policy digest and exact check outcomes before signing. Keep the
snapshot inaccessible to concurrent worktree writers; reject incomplete or
unknown input closure. Add a race test that changes the mutable worktree after
snapshot creation and proves the receipt still describes the executed bytes.

This also gates local signed-receipt reuse in GitHub: a protected collector
must independently resolve the current PR/merge tree, base policy, gate,
submodule and artifact identities. The existing observation matcher alone
cannot authenticate caller-supplied observations.

## Snapshot implementation constraints

A detached worktree is still writable and does not prevent child checks from
reading the original repository through inherited `SIMPLE_LIB`, HOME, network
or mutable caches. The signed lane needs a private source bundle materialized
from the exact Git blob objects, a copied and hashed native executable, and
an enforced read-only execution sandbox with only separate writable scratch.
The signer stays outside that sandbox. The receipt version must bind the
snapshot enforcement policy and execution platform as well as source and
binary identities; old signed claims cannot silently satisfy that stronger
contract. A warm cache may reduce preparation time only if its completed
bundle and identity are revalidated and immutable.

The current hook comments measured about 86 seconds to materialize and 26
seconds to remove a full detached worktree. Cold signed preparation therefore
cannot honestly fit its 60-second budget with that mechanism. A fast ordinary
hook and an explicit signed snapshot operation may use different budgets, but
both must account for all work before claiming a measured speed target.
