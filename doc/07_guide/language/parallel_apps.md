# Parallel Applications

Simple parallel code follows one default convention: the owner keeps canonical
mutable state; children read immutable input or receive explicit ownership;
children create independent results; the owner validates and commits them.

## Current contract surface

The repository now provides common vocabulary for transfer envelopes, storage
plans, access paths, parent-commit ordering, and assurance policy:

- child-created outputs are the preferred transfer direction;
- parent-owned mutable state is an explicit consuming move;
- process, remote, and device boundaries reject an ordinary owned in-memory
  region; they require an encoded/immutable handle or device lease;
- unknown dynamic ranges overlap until proven otherwise;
- external ABI/wire/MMIO storage remains pinned.

Critical policy denies implicit parent-to-child moves and dynamic transport, and
requires bounded mailboxes, deterministic commits, and frozen layout receipts.

The common commit engine now models a functional owner transition with a
constant-size final snapshot-root assignment. It first validates every result's base revision, identity, deterministic
order, and conflict policy. Only a fully valid non-empty batch advances the
revision and replaces the snapshot token. Failures return the original owner
state, and a shape-validated receipt records input/output roots plus the canonical task,
sequence, and payload-token order. The owning application adapter still builds
and verifies the candidate snapshot before supplying its token. A concurrent
runtime owner must serialize or CAS the transition against the live root; the
common value function alone is not an atomic synchronization primitive.

## Status

These are common/compiler contract foundations, not a claim that every current
actor, process, thread-pool, generic channel, or backend layout path already
enforces them. The snapshot transition does not itself interpret payloads or
run an application verifier. Runtime adapters, typed bounded public transport,
structured task groups, physical layout lowering, and end-to-end process/device
evidence remain work-package gates. Consult the receipt and the matching
runtime gate before relying on a path in production.

Actor mailboxes also have finite admission by default: zero or negative
capacity resolves to 256 rather than enabling an unbounded queue. A positive
capacity remains an explicit override. This prevents accidental unbounded
retention. The actor FIFO uses a bounded head cursor and compacts only when a
full backing buffer needs reuse; a native execution gate and typed public
backpressure receipt remain open.

The legacy actor mailbox now uses one class-backed state shared by copied
`ActorRef` and scheduler values. This repairs the previous copied-queue split,
and actor stop now closes that shared state before it discards queued work, so
future sends are rejected through every copy. This is still not an
ownership-safe actor transport: native send/ask routing, close wakeups,
cancellation, and typed transfer envelopes remain required.
Mailbox reads, fullness checks, and statistics now take the same state mutex as
enqueue/dequeue, and the mailbox exposes a retained-message high-water count
for bounded-memory evidence. That metric does not establish native actor
lifecycle or typed transfer safety.
The single-threaded actor scheduler also uses a consumed-prefix cursor for its
ready IDs. It reclaims a half-consumed large prefix in bounded batches rather
than slicing the front after every dispatch; this is an amortized scheduling
storage repair, not evidence of multi-threaded actor execution.
The scheduler itself is a class-backed authority. Every `ActorRef` retains the
scheduler that admitted it, so `spawn_on(custom_scheduler, ...)` send/ask/run
operations cannot fall back to the ambient global scheduler. References copied
from that actor retain the same routing authority. `ActorRef.stop()` uses that
same scheduler to drain queued asks and release their reply reservations before
the actor closes.
Each `Actor` is likewise class-backed: lifecycle state and error/dispatch
counters remain with the scheduler’s actor handle instead of disappearing in
value-array iteration.
Legacy `ask()` replies now reserve a finite scheduler-owned result slot at
admission. That credit remains consumed through handler completion until the
caller consumes or calls `cancel_ask(reply_id)`; an exhausted store rejects the ask rather
than silently dropping a completed result. This remains a scalar legacy actor
convention, not a typed transfer/parent-commit channel.

The scalar `BoundedChannel` implementation also uses a consumed-prefix cursor:
receive is normally O(1), and backing storage is compacted only when a later
send needs capacity. This retains its existing scalar sentinel API and does
not turn it into a typed task/process transport; task envelopes still require
their own ownership and lifecycle contract.

Parent commit order is independent of child completion order. The bounded
commit engine uses stable merge ordering, so equal keys preserve their
left-to-right input order while large result batches avoid quadratic selection
work. Payload application and concurrent publication remain owner-runtime
responsibilities.

`ParentCommitOwnerV1` is the current internal runtime owner for that root. It
serializes the live revision/token with a mutex and commits only fully
validated batches. Process-to-parent results use a framed, pointer-free `SPRS`
payload: the frame route/checksum and the typed result codec must both validate
before the owner builds a submission. `ParentCommitFrameInboxV1` provides the
matching parent ingress boundary. It copies accepted frames, rejects malformed
ones before retention, limits both frame count and copied bytes (16 MiB by
default), drains after close, and uses a head cursor rather than repeatedly
slicing the FIFO front. The parent may drain an explicit bounded batch and
commit it in one canonical transition. Its mutex-protected counters expose
accepted/rejected totals and frame/byte high-water marks for deterministic
bounded-memory checks.

`ParentCommitPipedResultReaderV1` is the bounded adapter for the existing
native piped-child stdout surface. It accepts only newline-terminated `SPRF1`
ASCII armor containing canonical lowercase-hex frame bytes, reassembles
partial reads, and passes verified frames into the inbox. It never decodes
arbitrary stdout as a frame, and it discards overlong lines through their next
newline rather than retaining unbounded partial text. Its default maximum line
matches the process-frame codec maximum; an application may pass a smaller
line budget, but cannot enlarge that transport bound.
Non-ASCII stdout is rejected before it is retained, keeping this an actual
byte bound even though the host pipe surface is `text`.
The reader also records its retained partial-line high-water mark, so a focused
memory gate can assert its maximum without relying on host RSS. That metric is
per reader lifetime and does not represent child-side or pipe-kernel buffering.
Closing the reader clears any partial line and makes later stdout chunks fail
at the reader boundary; a closed inbox alone is not used as a reason to retain
more child output.

This is still not an application process API or an implicit retry queue. Child
launch, stdin request protocol, cancellation, exit cleanup, and native
backpressure evidence remain application/runtime work. A frame is consumed
once the parent drains it; a stale or conflicting batch remains rejected and
the application must produce a new result against a new snapshot. The local
runner currently exposes only a Rust bootstrap seed, so native child delivery,
backpressure, and cleanup execution evidence remain required before using this
internal path as a production process transport.

WP-18 now has internal runtime groundwork for a deliberately narrow bounded
scalar pool-state pilot. Capacity counts pending, running, and completed but
unreleased tasks; credit returns only on release. Tagged generation handles are
pinned during runtime calls, so stale and wrong-kind handles fail closed. The
runtime ABI validates and copies a compiler-produced noncapturing direct-function
descriptor before returning from submit. This ABI is not public Simple API:
the attempted native facade spec timed out in the runner before a callback
assertion verdict, so end-to-end native Simple callback evidence and
alternate-provider execution,
language-enforced handle uniqueness, captured closures, heap results,
cancellation, blocking submit, and migration of legacy globals remain open.

The native runtime currently has one deliberately narrow heap-copy building
block: boxed `f64`, boxed `u64`, and immutable UTF-8 strings can be encoded by
logical content with a bounded `EncodedCopy` packet and reconstructed with a
new heap identity. This is not a general object-graph codec. Arrays, mappings,
tuples, objects, capabilities, device values, and unauthenticated remote routes
remain rejected until their schema, ownership, or lease contract lands.

The compiler also has an initial logical storage-access analysis. Given region
identities established by ownership analysis, MIR constant-index loads and
stores retain known half-open ranges, while dynamic indices, nested indices,
unbound pointers, and field paths remain conservative. Field names are useful
layout-planning evidence but do not yet prove physical disjointness. No current
backend may infer `noalias` or claim AoS/SoA lowering from these facts alone.

The layout advisory uses a separate typed terminal-event view. A conservative
record Load remains visible to ownership/conflict analysis, but is excluded
from locality counts only when all of its uses are direct field projections.
This deliberate difference never flows backward: a SoA recommendation cannot
prove field disjointness, ownership, or parallel scheduling safety.

Native typed-storage evidence is frozen as a deep-copied module-qualified
registry before cache lookup. The parent then creates immutable-lease class
capsules pairing MIR, storage sites, and compile identity; the builder callback
does not read mutable driver context or cache authority. Codegen revalidates
the complete MIR/storage identity around compilation, emits an object-hash
receipt, and a parent-only completion hook validates and checkpoints each
successful cache entry. The current
builder executes its batch sequentially, so this is concurrency-ready transport
parity, not real parallel `T[]` compilation. Process workers remain blocked on
a complete MIR-plus-storage codec.

The common storage contract also includes a checked reference conversion oracle
for fixed-size records. It can convert non-overlapping fields among AoS, SoA,
and tail-padded AoSoA plans and verify exact logical round trips. The oracle is
limited to 64 MiB, copies value-semantic byte arrays, and rejects malformed or
overlapping physical mappings. It is test evidence, not the optimized typed
array view or backend lowering promised by WP-22.

The compiler now has a first explicitly bound typed fixed-record host view.
Given the frozen storage plan, revision, element count, logical stride, and
exact field schema, it derives an overflow-checked affine address recipe:
`base + index * stride + field_offset` for AoS or
`base + column_offset + index * field_size` for SoA. The custom x86 native
selector lowers that canonical MIR intrinsic to real multiply/add addressing.
Address-observed or ABI-pinned records, malformed schemas, unknown fields, and
specialized layouts fail closed. This does not reinterpret ordinary dynamic
`T[]`; automatic typed-array allocation/binding and complete load/store
rewriting remain open.

Logical typed-view producers use `mir.storage.project_field.v1`. A late MIR
rewrite resolves an exact `(function symbol, base local)` sidecar entry before
emitting the validated affine address intrinsic. Missing or duplicate bindings,
dynamic field IDs, observed addresses, ABI-pinned plans, and unsupported layouts
fail closed. The site must also carry a proven index bound and a byte-capacity
that contains the maximum projected address. Driver-owned registration and a public `StorageView<T>` allocation
owner are still planned; ordinary arrays must not be inferred into this path.

The compiler driver owns these bindings per module for one compile session.
They freeze before parallel code generation, are removed with MIR eviction,
and their complete sorted semantics participate in native cache identity. The
rewrite happens atomically after generic MIR optimization and immediately
before backend dispatch, leaving canonical MIR unchanged on success or failure.
Current production admission is deliberately limited to custom-native x86_64
and 8-byte fields; other backends and widths fail rather than emitting a NOP or
using the wrong scalar load/store width.

Mapped-byte evidence uses the canonical exact-width `rt_ptr_read_u8` boundary.
The loader performs one direct copy into its result array; it no longer lowers
raw `*u8` dereference (which the current MIR path misclassifies) or builds an
intermediate slice. This also avoids an i32/i64 over-read at the last byte of a
mapping. A fresh runtime artifact containing the symbol is required before the
W^X parity scenario can be admitted again.

The MIR optimizer now also checks whether an AoSoA block is compatible with a
selected fixed-width SIMD route. Matching AVX/NEON-style widths are admitted;
AoS and SoA retain the scalar/reference fallback; ABI-pinned or mismatched
storage is rejected. SVE and RVV are recorded as explicitly deferred because
the native scalable-vector lowering path is not yet implemented. Admission is
only a legality gate: it emits no vector instructions, tail mask, or alias
metadata.

For admitted fixed-width plans, the optimizer can now derive a bounded physical
block schedule. Exact blocks are eligible for later vector lowering; a partial
last block always records its logical start/count as a scalar tail. The
schedule checks byte capacity, block budgets, forged admission shapes, and
arithmetic overflow. It never treats padded AoSoA lanes as logical elements and
does not manufacture a generic masked tail that current native backends cannot
yet prove safe.

A storage-aware emitter can now turn one proven full block into typed MIR SIMD
loads, arithmetic, and a store. It accepts only concrete MIR vector shapes and
only the OpenCL backend, whose lowering is exercised by an emitted-source
fixture. Callers pass pointers already projected to the requested physical
block and iterate only across `full_block_count`; scalar tails are never handed
to the emitter. Native x86/AArch64/RISC-V targets reject before emission because
their current selectors would otherwise reduce these operations to NOPs.

The x86 native route accepts only an explicit `native-x86_64-avx2` storage
selection with a 32-byte projection-alignment proof. It lowers f32x8 aligned
loads, Add/Sub/Mul/Div, and aligned stores through machine selection, low-eight
YMM assignment, scalar pointer allocation, and exact VEX encoding. Unsupported
shapes, missing alignment evidence, missing target-capability receipts, and
true overlapping vector pressure fail closed. Straight-line regions reuse
YMM lanes after a value's exact last use, so a chain may contain more than
eight destinations without manufacturing spill support. Multi-block SIMD
regions and calls are rejected because CFG liveness is not authoritative and
the supported SysV YMM lanes are caller-clobbered. A compiled-only system spec maps the emitted
bytes W^X, runs them only after the canonical CPUID/XGETBV AVX2 probe, and
checks eight exact f32 results plus unchanged input. CFG vector liveness,
32-byte aligned spills/reloads, high vector registers, and broader application
migration remain required before this is a production route.

## Recommended shape

```simple
val snapshot = owner.snapshot()
val results = TaskGroup.map(parts, snapshot, build_child_result)
owner.commit(results)?
```

Do not use a raw pointer or unclassified dynamic object as a cross-domain
payload. Do not infer that two different index variables are disjoint.
