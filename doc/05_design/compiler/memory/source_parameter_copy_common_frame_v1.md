# SOURCE parameter-copy common frame prerequisite

Status: source implementation and executable controls authored; execution is
UNRUN. Native prerequisite PR4871 has separate exact-source sanitizer evidence.
That evidence does not qualify this facade, compiler CFG, backend publication,
hosted/pure parity, 32-bit execution, or physical memory/performance bounds.

## Authority and ownership

The actual retained `SourceRegionRequestV1.context` owns the same mutable
`MirLoopResourceAccountV1` used by SOURCE lifecycle operations. The new leaf
`compiler.common.source_region_copy_frame_v1` reserves that account before
calling the existing native frame API. No caller-supplied account certificate,
Bool, reconstructed context, raw pointer, or common state value grants a pin.
Native control/generation/thread/module/lease/raw-birth checks remain authority.
All live-pointer entrypoints are unsafe and require compiler confinement.

Only one ordinary immutable flat-i64 Struct parameter copy is admitted by the
future caller proof. The actual field count determines `words`. The ordinary
copy remains a distinct heap allocation; this does not elide value copying or
change SOURCE mutation epochs. Native control storage already contains eight
copy-frame words charged by native create bounds. Two additional common
correlation fields increase facade creation from 12 fields/96 bytes/109 work
to 14 fields/112 bytes/127 work before creation.

## Frozen interface and order

| Common symbol | Inputs | Actual success |
|---|---|---|
| `source_region_copy_prepare_v1` | context, words | `Ok(0)` before ReadBegin |
| `source_region_copy_alloc_pinned_v1` | context | `Ok(positive untagged raw)` under actual lease |
| `source_region_copy_cleanup_pinned_v1` | retained request slot | `Ok(0)` after cleanup/cancellation |

Prepare prepays three bound observations, then reserves returned work, fields,
and bytes on the actual context account. Missing/unsupported provider results
refuse. Native preparation pays fixed frame, payload, raw-table growth and
cleanup before lease acquisition. Successful native ReadBegin binds its actual
lease, which the context retains. Allocation consumes the common attempt before
FFI; the native allocator also consumes its affine attempt before allocation.
An error remains cleanup-able and cannot fund a second allocation.

Compiler integration must branch on the actual allocation `Result` before any
field store, use its checked backend-specific Struct publication operation, and
route allocation errors through the consumer Result to wrapper cleanup. No
generic bitcast, unchecked pointer or enum reinterpretation is authorized.

On every wrapper exit (including failed ReadBegin, allocation/consumer failure
and abort), attempt copy cleanup before ReadEnd, revoke and release. Prepared
state with lease zero cancels once. Allocated or attempted state cleans while
retaining the lease/module exclusion until successful ReadEnd. The context's
states are absent/prepared/attempted/cleaned-awaiting-end; only successful native
transitions clear ownership. Without a copy frame, existing lifecycle behavior
is preserved. Native API refusal is never converted to cleanup success.

## Failure and explicit recovery

The wrapper attempts cleanup once, records the first cleanup error, continues
its existing lifecycle error protocol and returns the actual retained slot.
Pending copy state refuses ReadEnd/revoke/release before spending their credits.
Both semantic and cleanup errors survive. A failed cleanup can retain memory
and lease ownership; account exhaustion does not falsely report reclamation.

An explicit later cleanup call may retry with fresh work from the same account.
It prepays one observation, queries `copy_bound_v1(1, 0)`, rejects profile/bound
failure, reserves that work and makes exactly one native call. This bound is
conservative for any positive original field count: under the admitted plain
native64 profile cleanup scans frozen raw capacity and does not walk payload.
The first attempt consumes composite prepaid credit before FFI; retries never
replenish/refund it, rerun prepare/allocate, or loop automatically. Failed reserve
or FFI retains the frame and actual lease. Main Astra approved this design;
exact source acceptance remains separately recorded.

## Ownership and remaining gates

This lane owns the new common leaf, minimal context bookkeeping and pinned
cleanup facade. The parameter-copy compiler owner owns wrapper/lifecycle
declarations, actual checked allocation CFG and preflight/row integration.
Archive owner retains archive/hash/driver changes; no shared compiler type edits
are included. Main Astra performs independent source review. Additional
sidecars: N/A for this bounded prerequisite.

The activation gate remains closed pending actual same-account caller binding,
lexical confinement, backend checked edge/publication, no allocator escape or
callback during the prepared/leased interval, all-exit cleanup and runtime
profile exclusivity. Tests intentionally exercise real unsafe owners directly;
they cannot stand in for any of those compiler proofs.

Executable controls: `test/01_unit/compiler/source_region_copy_frame_facade_v1_spec.spl`.
Manual: `doc/06_spec/01_unit/compiler/source_region_copy_frame_facade_v1_spec.md`.
