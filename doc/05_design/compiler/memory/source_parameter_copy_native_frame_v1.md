# Native SOURCE parameter-copy frame prerequisite

2026-10-26; implementation base `92dd5a3b903`. Native prerequisite only. The
actual same-account common facade, wrapper all-exit cleanup, checked backend
allocation edge, hosted/pure providers, and generated Child(37) invocation are
OPEN. No capability bit, compiler gate, alias-elision or stack substitution is
enabled by these C entrypoints. New tests are authored UNRUN until the resource
owner approves a separate tiny fixture window. No physical RSS/time claim.

## Existing owners and private API

The existing SOURCE control embeds eight words of copy state: state, words,
birth serial, actual lease, raw revision, raw capacity, module generation, raw
pointer. Its existing control generation/execution owner are the outer identity.
Control creation charges its enlarged `sizeof` and eight added initialized
fields through the existing metrics queried by the existing account facade.
There is no new allocation registry, arena or dynamic frame buffer.

`rt_source_region_copy_bound_v1(words, metric)` returns a conservative complete
prepare/allocation/cleanup/end envelope. Metrics are work, fields and bytes.
`rt_source_region_copy_prepare_v1(control, generation, words, work, fields, bytes)`
recomputes current bounds before control lookup or growth and refuses shortages.
The actual SourceRegionContext account must reserve all three before invoking
prepare, before ReadBegin. Numeric C arguments are not account authority.

Preparation requires the composed native64 plain allocator, actual owner-thread
unpaused module, no live promotion-share window, no pending copy/lease/ticket,
and nonexhausted serial/revision. It prepares the existing raw table, installs
one exclusion pin and retains the post-pin revision. That TLS scalar prevents
teardown/rehash only; it cannot authorize a copy or select an allocation.
ReadBegin retains its existing epoch/lease checks and binds a prepared frame to
its actual successful lease. Region mutation epoch is unchanged by the copy.

`rt_source_region_copy_alloc_live_v1(control,generation,lease)` requires the
same genuine retained control pin as existing unsafe lifecycle calls. It checks
real frame/lease/module/profile/revision/capacity under the existing nonwaiting
region lock, then calls canonical `rt_alloc`. It records the pointer immediately
and pins its exact existing raw entry before returning. Failure returns a
negative status; compiler integration MUST add a checked edge before any field
store. Ordinary LLVM/Cranelift Aggregate currently lacks that edge, so it remains
unadmitted here. The returned pointer is untagged; backend tagging must follow
its existing canonical representation after success.

`rt_source_region_copy_cleanup_live_v1(control,generation,lease)` consumes the
actual frame's raw pointer, exact byte size, private raw-entry pin, module and
frozen capacity. It shares canonical allocator disposal with `rt_free`; it does
not guess tags, call a duplicate libc free, scan unrelated struct metadata or
claim a SOURCE-member birth. This bypass is valid only because this private
allocation is never registered as a struct/member or exposed to alternate frees.
The raw entry's existing ownership bit remains separate from the private pin.

## Lifecycle and refusal semantics

Prepared -> Ready (actual ReadBegin) -> Attempted -> Live (allocation) -> Cleaned -> Empty
(successful ReadEnd). Ready -> Cleaned handles nil/no-copy. The prepaid allocator attempt is consumed
before calling rt_alloc; failed allocation stays Attempted and can only clean,
never retry the allocation without a new prepared frame. Prepared + lease0 cleanup cancels once if ReadBegin did not succeed.
Cleanup errors preserve raw/frame/lease. ReadEnd refuses Prepared/Ready/Live;
revoke/close/release refuse every nonempty frame. Cleaned stays pinned until
ReadEnd clears frame and lease together. Ordinary no-frame lifecycle is unchanged.

Ordinary free/realloc/promotion cannot consume the pinned raw copy. Module/raw
scope pause/end and promotion-share begin refuse while its exclusion pin lives.
Raw growth and same-cap compaction refuse before replacing storage; allocation
callers roll back their new canonical allocation on registration refusal.
Unrelated insert/erase within the frozen table may change revision: allocation
requires its prepared revision, while cleanup intentionally uses exact pinned
identity instead of requiring an unchanged revision. No share window can become
live, so canonical raw unregister's share invalidation remains constant work.

The future actual wrapper must cancel on failed ReadBegin, clean on every
consumer Ok/Err/no-copy path before ReadEnd, and preserve the existing semantic
error independently of cleanup failure. It cannot return successful completion
while owning a frame. Cleanup refusal must retain the actual owner/lease; no
caller boolean, serialized witness or TLS flag substitutes for actual CFG proof.
Callbacks/tasks/reentry/nested allocation escape are outside the admitted slice.

## Cost envelope and evidence

Charges include frame/counter writes, payload zeroing and field copies,
raw-table allocation/zeroing, old-key rehash fields and worst-case collision
multiplicity, insertion/pin/rollback/erase probes over a conservative prepared
capacity, control qualification, and constant clear/unpin work. Freeze keeps
cleanup costs independent of future global struct-registry growth. Bounds are
logical, including allocator calls; existing malloc/free behavior is not a
finite physical latency promise. Guard/harden and noncomposed/non64 modes refuse.

The new actual-owner C fixture covers one-short work/fields/bytes, pending cancel,
lease/generation mismatch, a distinct copied value37, module/raw teardown and
ordinary free/realloc/promotion refusal, native64-only pin bit preserving ordinary
32-bit raw sizes, foreign thread and busy lock, failed
exact cleanup claim retaining the copy, actual frozen-table growth/compaction
refusal, stale preparation, injected canonical allocation failure before store and refused second attempt,
no-copy cleanup, exactly-once cleanup and absent/paused module rejection.
These controls are native prerequisite evidence only and currently UNRUN.
