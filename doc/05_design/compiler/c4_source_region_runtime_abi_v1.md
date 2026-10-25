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
| created_generation | immediate successful birth token | infallible generation; prepaid before create, compiler-sealed birth only |
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

Keep ordinary owner entries at their existing two-word size. A positive i64
extent leaves the high size_t bit free on this 64-bit provider: only SOURCE
entries use it to encode a checked aligned pointer to SOURCE-only metadata
{extent, region, generation, descriptor, control-kind}. All actual extent
readers decode through one canonical helper. Rehash preserves the encoded word
directly; ordinary frees do no additional identity lookup. SOURCE metadata
allocation is prepaid and freed once with its actual owner. Region generation
is checked on destination/child association and retirement, preventing a
recycled control address from admitting old allocations.

Rehash must preserve all metadata;
free/removal retires association before address reuse. Each provider is separate:
the struct extent registry cannot certify native container backing storage.

Existing insertion records a monotonic upper bound on successful probe count
within the probes it already performs; deletion retains that bound and rehash
resets/rebuilds it. Every present pointer is therefore within that bound, and
absence is proved by exhausting the same bound, even across tombstones. Exact
identity queries/stores prepay this owner-derived bound, not total registry
capacity. New pointer insertion still prepays capacity; there is no new cap.
Read/write operations never resize or traverse the registry. Reuse existing
owner locks through nonwaiting acquisition; contention is Incomplete. Prepay
every lookup including destination, control and incoming child separately.
The complete commit bound must be reserved before write_begin; commit performs
no callback/allocation/resize and validates the immediate child before store.

Allocation registry growth requires a separate construction preparation before
allocation. Its bound must include old-capacity traversal and worst-case rehash
insertion probes, checked multiplication and metadata bytes. A stale prepared
registry revision cancels without allocation/publication. A store prepays the maintained maximum-successful-probe bound; it never pays
for registry resizing. The native memory-owner route
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

Revised production source e7fc605f056 received independent SOURCE_GO with no
P0/P1 findings. The composed native active-transient and standalone primitive
binaries both passed under AddressSanitizer and UndefinedBehaviorSanitizer.
Standalone additionally executed foreign-thread raw member retirement, proving
that it revokes the original region and permits final control release. These
are C primitive assertions, not SPipe or compiler/HIR acceptance. Native containers, pure and hosted provider admission
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

Representation 2 is supported only for an exact compiler-certified Struct edge:
require low tag bits exactly 1, normalize the owner lookup, and preserve the
original tagged word in the store. Zero cannot be committed to a nonnullable
Struct edge; zeroed constructor storage is not a completed published value.

## Executed primitive evidence (2026-10-25)

The final composed-native attempt used:

```sh
cc -std=gnu11 -O0 -g -fsanitize=address,undefined -ffunction-sections -fdata-sections -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -pthread test/01_unit/runtime/runtime_source_region_v1_test.c src/runtime/runtime_native.c -Wl,--gc-sections -ldl -lm -o /tmp/simple-c4-provider-native-reviewed-test
/tmp/simple-c4-provider-native-reviewed-test
```

The final standalone attempt used the same sanitizers, linked the test's actual
included memory owner without runtime_native.c, and produced
`/tmp/simple-c4-provider-standalone-reviewed-test`. Both exited 0 with
`C4 raw struct primitive: PASS (full SOURCE UNRUN)` and no sanitizer findings.

The six-attempt budget is exhausted: five primitive passes across evolving
revisions and one repaired intermediate compile error. Do not rerun green checks.
Native active scope rejects a foreign raw free at its existing owner boundary;
standalone permits that route and exercised the revised any-owner retirement.
Actual forced same-address control reuse was not executed. Lifetime-generation
mismatch was executed; lingering-member control-address ABA is covered by the
reviewed generation-association checks, not an allocator-reuse execution claim.
Ordinary compiler startup/RSS/store performance and full parser/HIR constructor
acceptance remain UNRUN. Containers, immutable text certification, pure/hosted
providers, guarded/hardened allocators and cross-thread borrowed-load confinement
are OPEN. Nothing here upgrades whole SOURCE capability.
