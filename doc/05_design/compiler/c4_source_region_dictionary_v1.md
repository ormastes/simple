# C4 typed dictionary owner integration v1

Status: interface frozen with architecture/planner owners; implementation
candidate present. Baseline dictionary fixture was RED (missing native APIs);
its first implemented revision passed ASan/UBSan. Exact candidate review and
post-review evidence remain pending. This first i64/Struct milestone is
partial. It does not admit HIR roots, text keys, arrays/enums/bytes, pure/hosted
providers, caller/pin/link closure, or whole SOURCE.

## Compiler-facing freeze

The existing four-argument `rt_source_region_bound_v1(operation, descriptor,
capacity, metric)` gains operations 13 new, 14 put, 15 remove, 16 get. Existing
1–12 and separate private live-cleanup operations are unchanged. Metrics retain
0 work, 1 state fields, 2 allocation bytes.

| Native export | Arguments | Result |
|---|---|---|
| rt_source_region_dict_new_v1 | control, generation, expected_epoch, descriptor, capacity_hint, work | ordinary tagged dictionary handle or negative error |
| rt_source_region_dict_put_v1 | control, generation, expected_epoch, dictionary, raw_i64_key, struct_bits, work | original success flag 0/1 or negative error |
| rt_source_region_dict_remove_v1 | control, generation, expected_epoch, dictionary, raw_i64_key, work | original removed flag 0/1 or negative error |
| rt_source_region_dict_get_v1 | control, generation, expected_epoch, dictionary, raw_i64_key, work | 0 absent, positive nonnull exact Struct bits, negative error |

Dictionary birth preserves ordinary `rt_dict_new`: the hint is ignored and the
initial capacity is eight. Put/remove keep their semantic flags; epoch lives in
the region and an observer uses separately prepaid stamp operation 4. Same-value
put advances epoch once. An absent remove returns zero without advancing epoch.
No op17, packed epoch/flag codec or mutable last-result accessor is introduced.

Facade names are `source_region_dict_{new,put,remove,get}_v1`. New/put/remove use
`Result<i64,E>`; get uses canonical `Result<Option<i64>,E>` with `None` for native
zero. Zero/nullable Struct values are not supported, so absence cannot alias a
valid stored value. Keys preserve all original i64 bits, including extrema;
capture happens before boxing and typed hashing/equality allocates nothing.

## Exact shape-four descriptor

The six-u64 readonly compiler-owned header is `[1,4,64,2,table_address,1]`.
The key row is `[0,8,1,0]` (exact raw i64 scalar). The value row is `[8,8,2,R]`,
where R=1 exact raw Struct pointer or R=2 exact Struct tag-one representation.
The 64-byte extent describes `RtCoreDict`, while row offsets zero/eight describe
key/value in each 32-byte `RtCoreDictEntry`, not fields of the header. Provider
checks actual sizeof/offsetof and the exact shape-specific grammar. It never
uses generic Struct slot GEPs for dictionaries. Dynamic/Any and nullable values
fail closed. Tagged values require tag bits exactly one; lookup normalizes the
identity and storage preserves the original tagged bits.

## Paid observation before metric requests

For operations 14–16, the bound's descriptor argument is the actual dictionary
handle and capacity argument is an already-prepaid dictionary-observation
allowance. New private `rt_source_region_dict_observation_bound_v1()` reads only
the existing owner's scalar maximum successful probe watermark under a trylock;
it does not look up or dereference any dictionary. Its request costs fixed one.

The facade prepays that fixed request, checks returned allowance positive and
checked `3*allowance`, reserves that work on the same shared account, then makes
the three metric requests. Each validates the current required allowance BEFORE
any membership probe/header access. A grown owner watermark refuses Capacity
without a probe. Only paid membership success permits reading actual capacity,
shape and anticipated backing growth. Each real operation independently prepays
and revalidates its own lookup, key work, collision bound, copying, allocation,
typed edge validation and epoch update. Zero/overflow/incomplete observations
publish no authority. Operation13 uses its trusted readonly header and ignores
the ordinary capacity hint; its bounds include registry/list growth preparation.

Insertion updates the existing immortal registry's conservative maximum
successful probe count inside its already-running probe loop. Tombstone reuse
retains the upper bound, and resize resets/rebuilds it from every insertion.
No new collision cap or registry is added. Metric observations do not silently
perform an unpaid registry scan or reserve global worst-case backing bytes for
every small dictionary.

## Native owner association and lifetime

`RtCoreDict` stays 64 bytes, entries stay 32 bytes, and existing immortal registry
entries stay one pointer. Only SOURCE entries encode an aligned 16-byte owner
record with alignment tag2; that record authenticates the actual dictionary and
its current live backing before any prefix dereference. Ordinary entries remain
raw pointers. All membership/hash/erase/rehash/scope-reader consumers decode the
actual pointer canonically. SOURCE-only flag bit0x80 identifies a backing allocation
with an aligned SOURCE-only prefix holding control, generation, descriptor,
actual dictionary identity and ABI version. `entries` still points to actual
slots; only SOURCE allocation/free/rehash subtract the prefix. Ordinary memory
layouts/allocations remain unchanged. No ordinary object can be attached later.

Prefix+`32*capacity` arithmetic is checked and prepaid. Rehash builds a complete
fresh backing with the same owner identity, copies only actual occupied slots
under prepaid probes, and publishes the new backing after successful preparation.
It never reinserts through generic mutation hooks or advances epoch per copied
row. Publication also updates the existing-entry owner record before the old
backing is freed. A copied header has no SOURCE owner record: typed operations
reject it before reading entries/prefix, and native retirement frees only its
independently registered header without touching a borrowed/dangling backing. Destruction frees the actual prefix and decrements region membership once
through the existing native owner lifetime. Initial birth requires an actual
active, unpaused native transient scope; other lifetime routes remain Incomplete.

Generic mutation paths reject SOURCE dictionaries before any store when no
classified/prepaid context exists. Typed get uses raw-key hashing/equality;
generic boxed-key lookup cannot read this backing as if it held tagged keys.
Deep-free/promotion routes cannot retrospectively adopt/walk a source graph to
establish authority. All unclassified compiler effects remain admission blockers.

## Runtime-owner critical section refinement

The native provider validates actual dictionary membership/prefix under its
existing nonwaiting immortal-owner lock. A C-runtime-only region-owner bridge
then obtains the existing nonwaiting region/allocation-owner lock, validates
control/generation/saved epoch/conflicts and the immediate incoming Struct edge,
and retains that lock across the exact native operation and epoch update. There
is no user callback or fallible reservation between store and epoch advancement.
All fallible allocation/copy preparation precedes publishing dictionary changes.

This bridge is not a SOURCE intrinsic or an admitted raw FFI surface. Its entered
lock state cannot be fabricated by Simple caller values. Compiler-facing symbols
are only operations13–16 above. Birth installs the prefix before publishing the
tagged handle and increments the existing control's member count. Retirement
checks the stored generation, atomically revokes, and decrements once. Reuse of a
control address cannot attach old dictionary storage to a new generation.

## New acceptance and limits

The new fixture must retrieve a born Child through actual typed dictionary get,
retain that alias before saving a stamp, mutate the Child alias, and observe
Stale against the saved region stamp. Additional new controls cover same-value
put, remove/reinsert, absent remove/read, actual backing rehash, both Struct
representations, extreme i64 keys, foreign/preexisting/null value refusal, and
fuel-one-short leaving contents/epoch unchanged. Real existing native retirement
must release the dictionary member once. No exhausted primitive/cleanup test is
re-run; this is a distinct dependency fixture, scheduled through root.

Actual HIR `SymbolTable.new` currently constructs dictionaries/root scope before
attachment. It requires specialized genuine birth, text-key ownership, optional
parent, enum kind and all actual roots/transport writes before admission. The
i64 milestone does not certify those missing dependencies or replace any of the
three original name/type/parent Stale controls. Existing ordinary constructors
remain unchanged.

Native-owner entry now retains the existing region lock, with only direct
observed calloc/realloc and existing lock-aware registry resize/insert helpers
inside the critical section. It never calls rt_alloc, a user callback or a
reservation callback there. The optional dictionary reader identity uses one
strong atomic attempt; contention fails explicitly instead of spinning. Native
retirement holds the dictionary registry lock before taking the region lock.

Separate reverse Struct-to-Dictionary representation4/operation17 is approved
as a future extension but is not implemented or admitted by this13–16 milestone.
Ordinary7/8/9 remain exact Struct routes. Actual SymbolTable dictionary fields
therefore remain rejected, not mislabeled as Struct pointers.

New dictionary attempt accounting: baseline RED1 is retained in
/tmp/c4-dictionary-red.log; first implemented ASan/UBSan PASS2 is retained in
/tmp/c4-dictionary-attempt2.log. Later source boundedness hardening is awaiting
review; the old six-attempt primitive and one-attempt cleanup runners were not
called. No actual Simple shared-account/HIR/pin/link/performance verdict follows.

## Copied-owner and ordinary-path review repair

Source review of ce0d1ca442e found the missing ordinary-clear guard and that a
prefix identity check alone could dereference an already-freed backing. The
repair adds the actual SOURCE-only owner record to the existing pointer slot,
never another registry. Native erase obtains that record from the matched entry
and retires its live backing under the existing owner lock before freeing it;
uncertified copied headers never enter prefix retirement. Birth metrics include
the extra two fields/16 bytes, and rehash changes the same record's backing.

The new fixture makes two genuine registered ordinary headers and deliberately
copies a SOURCE header into them. One retains a backing subsequently freed by
rehash; the other is retired after the original source owner. It also exercises
ordinary clear refusal with unchanged contents/epoch and a second real native
scope for tagged-record erase/reinsert and old-owner rejection. Actual address
reuse is reported if observed, not assumed from a new generation alone.
