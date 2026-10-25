# C4 runtime ABI refinement v1

Status: private ABI frozen with architecture approval; provider implementation OPEN.
No compiler/HIR SOURCE admission or execution PASS. This refines the source-region contract;
the typed account facade is not a literal C account-pointer interface.

## Boundary and ownership

The compiler-private Simple facade retains the existing shared resource account
and the opaque native control token. Each operation obtains its provider bound,
reserves through that same account, and immediately executes the private native
primitive. Numeric fuel is a consumed work allowance, not a proof of reservation.
Closure admission must reject raw calls, unknown instrumentation/context, unsafe
mutation and unclassified call effects. No user callback enters the provider.

Use signed 64-bit scalar arguments/results on the existing FFI boundary. Success
handles, generations and epochs are positive; 0 is successful void. Errors:
`-1 Incomplete`, `-2 ForeignOwner`, `-3 Stale`, `-4 Capacity`, `-5 Closed`,
`-6 Conflict`, `-7 Consumed`. Never encode a heap value in an error channel.

## Exact descriptor words

Descriptor metadata belongs to compiler-sealed, artifact-owned immutable storage;
it is not a caller-owned rich object or a user-authored assertion of provenance.
All words are u64 in target native byte order, with eight-byte alignment:

| Word | Meaning |
|---|---|
| 0 | ABI revision = 1 |
| 1 | shape: 1 struct, 2 enum, 3 array, 4 dictionary, 5 mutable bytes |
| 2 | exact allocation extent in bytes |
| 3 | slot count |
| 4 | slot table address |
| 5 | compiler instrumentation ABI identity |

Each slot is four u64 words: byte offset, byte width, edge kind, representation.
Edge kinds: 1 scalar, 2 same-region mutable allocation, 3 certified immutable.
Representation 1 is untagged native pointer, 2 native tagged heap pointer; scalar
representation is 0. Unknown combinations fail Incomplete. The initial struct provider requires exact native-word eight-byte slots; mutable edge width must
equal target pointer width. Bounds
use subtraction before addition. A descriptor with unclassified padding or
pointer-bearing storage cannot enter SOURCE. Tagged/dynamic values require a
provider-specific checked classification, not masking and guessing.

## Scalar export schema

All names begin `rt_source_region_` and end `_v1`:

| Middle name | Arguments | Result |
|---|---|---|
| abi | none | 1 |
| capabilities | none | supported representation bits; full SOURCE admission is separate |
| bound | operation, descriptor, capacity, metric | metric 0 work / 1 state fields / 2 allocation bytes, or error |
| create | prepaid_work | control token |
| allocation_prepare | descriptor, capacity, prepaid_work | prepared registry revision |
| alloc | control, generation, epoch, descriptor, capacity, prepared_revision, prepaid_work | allocation identity |
| generation | control, prepaid_work | lifetime generation |
| stamp | control, generation, prepaid_work | epoch |
| read_begin | control, generation, epoch, prepaid_work | lease serial |
| read_end | control, generation, lease, prepaid_work | 0 |
| write_begin | control, generation, epoch, destination, slot, prepaid_work | ticket serial |
| write_commit | control, generation, ticket, value_bits, prepaid_work | new epoch |
| alias_write | control, generation, destination, slot, value_bits, prepaid_work | new epoch; never refreshes saved HIR stamp |
| close | control, generation, prepaid_work | 0 |
| release | control, generation, prepaid_work | 0; only after all consumers end |

The bound operation numbers follow table order starting at create=1; alloc=2,
generation=3, stamp=4, read_begin=5, read_end=6, write_begin=7,
write_commit=8, alias_write=9, close=10, release=11; allocation_prepare=12. Descriptor/capacity are zero
except alloc and allocation_prepare. Bounds do not authorize operations and cannot mutate/adopt graphs.

## Existing owner association and bounded operations

Extend existing owner entries with control identity, allocation incarnation,
descriptor identity and control-record kind. Rehash must preserve all metadata;
free/removal retires association before address reuse. Each provider is separate:
the struct extent registry cannot certify native container backing storage.

Prepay the existing registry capacity per identity lookup, then probe at most
that capacity with early termination. There is no additional collision cap.
Read/write operations never resize or traverse the registry. Reuse existing
owner locks through nonwaiting acquisition; contention is Incomplete. Prepay
every lookup including destination, control and incoming child separately.
The complete commit bound must be reserved before write_begin; commit performs
no callback/allocation/resize and validates the immediate child before store.

Allocation registry growth requires a separate construction preparation before
allocation. Its bound must include old-capacity traversal and worst-case rehash
insertion probes, checked multiplication and metadata bytes. A stale prepared
registry revision cancels without allocation/publication. A store prepays full existing-capacity lookup bounds in this correctness
baseline; it never pays for registry resizing. The native memory-owner route
now prepares both existing registries before
allocation, retaining one TLS preparation record and rejecting changed raw or
struct revisions. Guarded/hardened allocators remain Incomplete.

## Lifetime and failure

One embedded active write ticket; monotonically increasing lease/ticket serials.
Single-owner execution; read/write conflict rejects before mutation. Generation,
epoch and serial exhaustion are sticky Capacity, never wrap. Same-value stores
advance epoch. Close revokes reads/writers before reclamation. Read-end may
consume an outstanding lease after close; release rejects active consumers.
The control must remain in its existing owner until release. A recycled address
cannot reuse generation/incarnation. Foreign/preexisting mutable children are
rejected; region attachment/adoption is absent from this ABI.

## Capability and evidence status

Native raw-struct primitive tests PASS in standalone and composed native
active-transient modes. Native containers, pure and hosted provider admission
remain UNRUN/OPEN. Full parser/HIR SOURCE acceptance remains UNRUN. None may
advertise full closure from per-allocation epoch checks.
Every unsupported provider must return Incomplete before authority or mutation.
Positive primitive tests do not establish real parser/HIR constructor acceptance.
No heavy tests while the canonical build resource owner holds its lease.

The facade prepays three fixed-header bound observations, reserves their work,
state fields and bytes once on the shared account, then invokes the operation.
Full slot classification runs only after that reservation. Work includes
metadata scan, actual registry growth and all metric category charges. Alias
work covers the combined stamp/begin/commit operation, not three reuses of a
small allowance. Native operations revalidate live bounds under the existing
nonwaiting owner lock before any paid scan, allocation or mutation.
