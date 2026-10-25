# Actual SOURCE request pin verification boundary v1

Status: contract frozen with the authority owner; generated wrapper, emitted
context confinement and wrapper CFG analysis are source-implemented, UNRUN.
Request admission remains OPEN. This document issues no pin receipt and enables
no direct live-pointer cleanup operation.

## Authority inputs

The invocation's actual resolver owns the request declaration, context
declaration, private facade declarations and specialized producer entry
SymbolIds. A caller-created `SourceRegionFacadeSymbolsV1`, matching text name,
SHA-256-shaped string or runtime `live` boolean is not that authority.

Reuse `ResolvedDirectCallCaptureV1` from actual lowering: owner SymbolId,
block ID, instruction index and callee SymbolId. Bind captures to finalized
instruction sites, signatures and bodies before analysis. Generated calls
require generated captures from the same owner; textual MIR calls cannot be
resolved afterward to manufacture provenance.

The existing whole-module Verification 2.0 finalizer requires executable
internal targets. It cannot certify native externs by inventing internal
bodies. Native boundary admission must separately bind the actual canonical
private ABI declarations and reject every unclassified external call.

## Required actual flow

1. Trusted `create(account)` returns `Result<Context,E>`. Only its validated
   canonical Ok extraction introduces a fresh live owner. Err introduces none.
   A class literal, parameter or arbitrary Result payload is not a birth.
2. A hidden context argument is a scoped borrow only when the resolved callee's
   actual body and exits are verified to retain no alias. It creates no second
   owner. Reject copying, reconstruction, capture, global/field/container store,
   return and unknown call of the context or its native control/generation.
3. Successful read-begin introduces an exact lease and separately prepaid end
   credit. Every exit ends it once or transfers it into the actual retained
   request cleanup state. Unknown branch outcomes cannot erase obligations.
4. Successful revoke marks revoked. It does not end leases, release graph
   members or consume the pin.
5. Each release attempt consumes its own prepaid credit. Success consumes the
   live owner before subsequent direct-native use; failure retains the owner
   and separate cleanup error. Failure cannot return a bare error that loses
   the only owner. There is no implicit retry or eventual-free claim.

Analyze actual CFG edges and joins, including creation failure, producer
failure, read-end failure and release failure. Conflicting owner/lease facts
at a join fail closed; unreachable blocks cannot supply missing cleanup.
Mutation of a body, call binding, context local or declaration invalidates the
admission. A conditional region-frame theorem is not executable refinement.

## Fixed private native boundary

`rt_source_region_live_cleanup_bound_v1(operation, metric)` uses operations
revoke=1, read-end=2, release=3 and work bounds 16, 24, 64. Fields and bytes
are zero. Actions are `rt_source_region_revoke_live_v1(control, generation,
work)`, `rt_source_region_read_end_live_v1(control, generation, lease, work)`
and `rt_source_region_release_live_v1(control, generation, work)`.

These direct pointers are unsafe until the actual executable pin proof above
is validated. Generation comparison cannot make a freed pointer safe. No
ambient registry, global graph walk or replacement runner is authorized.

## Current source blockers

The saved authority wrapper exposes caller-constructible `SourceRegionRequestV1`
and `SourceRegionContextV1`, returns a rich request from create, invokes an
indirect producer function value, and splits cleanup across public methods.
The existing specialization forwards the hidden context with a MIR Copy
operand. That operand can represent a scoped ABI borrow only after callee
confinement is established; metadata alone does not establish confinement.

The new generator creates a fresh private typed HIR function and lowers it with
the actual session's `lower_function`. It accepts direct resolved producer and
consumer identities, borrows the existing retained slot, invokes those bodies,
and executes finite read-end, revoke and release attempts. It returns
`Result<Result<i64,E>,E>`: only actual release Ok constructs outer Ok. Semantic
first error and first cleanup error remain independent; cleanup Err replaces
only semantic Ok. No context, slot or rich producer result is returned.

The actual caller must canonical-create the slot, authenticate Ok, and move it
into the invocation's retained field before wrapper borrowing. Only the
authenticated outer Ok permits clearing that field; outer Err retains the live
owner. The existing public callback wrapper remains unadmitted.

`source_region_context_confinement_v1.spl` checks actual emitted context uses
against actual canonical callee captures. `source_region_request_flow_v1.spl`
checks finite CFG paths, actual Result discrimination, typed payload provenance,
cleanup ordering, first-error selection and released/retained outcome joins.
Unsupported instructions and calls fail closed. Neither helper alone is a pin
receipt: actual caller retention, closed callee bodies, fixed-credit facade
refinement and canonical builtin emitter-site capture remain composition gates.

The CFG verifier takes the actual owning invocation account. It rejects absent
or closed accounts, and prepays cumulative work/state/byte charges before scans,
complete map/path copies, path forks and retained queue growth. Processed states
remain charged; no quota is reset or refunded. The builtin finalizer must use
that same account before its scans and digest allocations. Structural ABI
comparison uses an accounted iterative type worklist instead of uncharged
recursive JSON rendering. Capacity produces no receipt. Container allocation
and RSS qualification remain separate obligations, not inferred from logical
slot charges. All Cast and Bitcast instructions are rejected until an exact
lossless codec conversion policy exists; preserving a source ID cannot certify
that an i64-to-Bool-to-i64 conversion preserves its value.

Result codec primitives require lowerer-origin typed site captures distinct
from resolved source calls; no invented builtin SymbolId or textual name can
replace them. That capture producer and the actual caller integration are owned
by the context-transform lane. Positive evidence must exercise the actual
generated and admitted request path; negative evidence must exercise copies,
escapes, forged birth and use after release through the same entry. No
straightline surrogate, fabricated flow rows or gate-only test substitutes.

No heavy tests were run. Full SOURCE, containers, pure and hosted providers,
and a global compiler ownership guarantee remain separate open obligations.
