# SOURCE immutable text provider contract proposal

Status: PROPOSED, awaiting Astra ABI/physical review. No schema, native operation,
compiler recipe or SOURCE admission is enabled by this document. Actual tests
are UNRUN. This contract extends the existing region/request owner; it creates
no separate text-release authority.

## Existing owners and duplication findings

The native owner is `runtime_native.c`: `RtCoreString` has kind/reserved/length
and inline bytes with a16-byte fixed header. `rt_string_new_uncached_impl`
allocates the actual `16+n+1` extent and knows `n` before publication. Ordinary
registration stores a pointer in the existing immortal registry. That registry
already supports tagged SOURCE dictionary registration metadata; extend that
same entry-dispatch mechanism for text rather than adding another registry.
The short-string cache, literal intern table, `SHARED` bit and ordinary pointer
membership do not attest immutable input provenance. Existing allocations
without birth metadata cannot be upgraded retrospectively.

Relevant lifecycle owners are registration/unregistration, transient scope
tracking/end/promotion, `rt_string_free`, deep-free classify/commit, and
`rt_string_data`. These must be audited together before implementation GO.
The backend owner confirms no existing retained loaded-literal mapping owner;
final ELF file-byte seals do not certify live mapped addresses.

## Candidate numeric assignment, not a reservation

Propose shape6 and physical text representation6, distinct from mutable bytes
shape5 and existing Struct1/2 and Dictionary4 recipes. Descriptor words are
`[1,6,16,0,0,1]`. Zero rows are valid only for this exact immutable-text shape;
ordinary Struct zero-row refusal is unchanged. Native sizeof/offsetof checks
must verify the fixed prefix. Dynamic byte extent never comes from header.len.

Propose region operation IDs18–21 for text copy, length, byte and equality;
22–25 for text-key dictionary birth/put/remove/get;26 for authenticated input
span derivation. ABI owner must check all outstanding byte/array reservations
before assigning these numbers. Dictionary text->i64 and text->text use distinct
compiler-owned recipe discriminators; neither silently reuses shape4 grammar.
No implementation may rely on these numbers before explicit ABI review GO.

## Authentic dynamic input birth

An ordinary HIR text value, pointer/length pair, hash, text tag or registry
membership cannot mint a StableSpan. Recording extent at ordinary allocation
birth is necessary but insufficient: `rt_string_data` may already have exposed
a writable alias. Pinning that allocation prevents free but cannot revoke a
previous alias or exclude concurrent writes.

The concrete proposed ingress is the actual invocation's retained source/file
read owner. It must allocate its snapshot through a private stable-input birth
path BEFORE returning text or any raw address. The native allocation owner
records true allocation extent, authoritative byte count, fixed header layout,
birth revision, frozen state, never-raw-exported state, invocation owner binding
and pin state in the existing registry entry. The read owner writes bytes only
before freezing; its observed snapshot defines the actual compilation input.
No public pointer-based registration API is provided. Existing ordinary
`rt_file_read_text` output is NOT accepted merely because it came from a file.
The driver/read owner must opt into this private path and retain the actual
snapshot handle in its invocation owner before parsing starts.

Lexer/HIR text spans then derive from that retained snapshot or another
already-authenticated frozen birth, using checked subranges. Derived token
identity binds native entry, birth revision, offset/length and actual invocation
lifetime, not caller-authored fields. No separate token registry is needed:
the token is an owner-internal handle to retained existing-entry metadata.
Account/storage growth for handles and source bytes is prepaid by that same
invocation's actual account. Admission remains Incomplete until the real read,
lexer substring and HIR text publication paths carry these handles.

For literals, the only admissible future route is a retained loader mapping
owner binding admitted file identity, read-only mapped segment, relocation,
exact address/range and live mapping lease. The current file seal does not
supply it. Literal route therefore remains Incomplete; neither pointer bits nor
literal tags select a shortcut.

## Typed operations and publication

Compiler-private `StableSpan` is opaque to source values. Proposed facade:

* `text_copy(context, span, offset, length) -> Result<text,E>`
* `text_length(context, saved_epoch, text) -> Result<i64,E>`
* `text_byte(context, saved_epoch, text, index) -> Result<i64,E>`
* `text_equal(context, saved_epoch, left, right) -> Result<bool,E>`

Native bounds/prepare/copy use scalar owner handles internally, never arbitrary
pointer inputs. Bounds authenticates span metadata and checked subrange before
reading bytes. Reserve on the actual account, then pin source, allocate fresh
uncached storage, copy/hash exactly n bytes, set terminal NUL, install frozen
registry metadata and same-region membership BEFORE publication. Include the
terminator in allocation extent but not logical equality/hash input; embedded
NUL and nonASCII bytes remain ordinary content. Empty text has a real owned
birth and never promotes a shared empty-string cache. A failed reservation
publishes nothing; stale revision or failed nonwaiting lock returns a typed
error. All rich text/Option Results use canonical owning codecs and real Err
CFG. Scalar result-layout guessing is forbidden.

## One canonical lifetime

SOURCE text registration retains region control/generation, authoritative
extent/length/hash, frozen revision and member status. Dictionary remove,
replace, clear and backing rehash change associations only: text remains owned
until canonical region/request retirement, including retained query aliases.
No dictionary reference count authorizes early text free.

Public raw-data APIs refuse SOURCE addresses; a bounded typed read lease is the
only admitted byte access. Public free/unregister/deep-free planning must refuse
SOURCE text while retained, without partial graph destruction. Transient
teardown/promotion must neither unregister nor detach SOURCE entries. Internal
canonical retirement drains each member once, records revocation, unregisters
and frees backing/metadata under the existing native-owner -> region-owner lock
order. Outstanding leases or failed cleanup retain the actual invocation owner.
Release succeeds only after all members and leases drain. No
`text_release_request` operation exists. Public state flags are not release
authority. Every raw/FFI effect that might mutate/free/expose text is rejected
before SOURCE entry unless explicitly modeled by these owners.

## Charged collision and lock contract

Use only lock-held native hash/equality/registration helpers while the existing
native registry/dictionary owner lock is held; then acquire the region owner
nonwaiting in existing order. Never call public lock-acquiring hash/equality,
allocate, reserve, invoke user callbacks or block on region acquisition while
holding that lock. Preparations needing allocation/reservation happen before
lock entry; revision mismatch retries require a newly prepaid attempt.

Define native authenticated observations: registry capacity R (including
tombstones), dictionary capacity D, maximum registered key byte length M,
query byte length Q, and replacement backing byte count B. M is maintained at
authenticated birth/insertion, monotonically conservative until paid rebuild;
it is not discovered by an unpaid query scan. Native bounds snapshots and
revision bind these values; mutation invalidates prepare. Registry growth must
include old/new capacities and worst reinsert collisions, not live count alone.

Proposed conservative work envelope for a dictionary observation attempt is
`K + 8R + 8D(R+1) + 4D(Q+M+1) + 4Q`, with checked arithmetic throughout.
It covers qualification, every visited probe's ownership check and full byte
comparison on hash collision; hashes never establish identity. For mutation,
add `8D²(R+1) + 4D²(M+1) + 4B` for adversarial rehash/copy and retirement work.
K and fixed metadata field counts must be derived from actual native paths
before ABI GO; these are reviewable upper-bound candidates, not calibrated
performance claims. All allocations charge actual metadata/backing extent plus
replacement overlap; failed attempts consume work credit without refund.
Text copy separately prepays `Kcopy + 8R² + 4n` work and `16+n+1` backing bytes
plus exact registry metadata/growth overlap, before any byte read or allocation.
Query hash reuse is allowed only from authenticated frozen metadata; forged
header length/hash, stale spans and foreign generations fail before dereference.

## Implementation gates

Astra must freeze numeric IDs, physical metadata entry layout, lock/cost paths
and canonical retirement compatibility. Then implement authentic input birth
and actual driver/lexer/HIR handle transport, native free/deep-free/transient
refusal, typed compiler recipes and both backend/seal schemas. No partial
provider capability may advertise text support before all corresponding gates.
Required authored/executed evidence includes one-short no-publication, equal
bytes in different births, embedded NUL/nonASCII, collision equality, forged
len/extent, old ordinary text refusal, prior raw escape refusal, transient and
deep-free pin protection, replace/remove retained alias and release failure.
Until those gates close, full HIR text/dictionary graph support remains OPEN.
