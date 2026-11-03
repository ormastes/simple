# P0 ownership and freeze primitive inventory

Base inspected: `4fccb94e564b25a0a2effdd711113da5a1b1e20c`, isolated
`/tmp/simple-targethir-foundation-20261103`. Scope: read-only source audit for
the governing immutable HIR/TargetHIR plan. No compiler/runtime source edits,
builds, tests or benchmarks were performed. Experimental host-view worktrees
are not evidence for this inventory.

Applied `.agents/skills/parallel-ownership/SKILL.md`: distinguish copy, frozen
share, owned move, scoped loan, handle and encoded-copy boundaries; a semantic
contract does not establish runtime transport or memory safety.

## Evidence levels

“Implemented” below means a concrete implementation body was inspected. It
does not mean native execution, cross-platform correctness, or race freedom
was verified in this audit. Existing specs are candidate validation assets,
not inherited PASS receipts.

| Surface | Evidence at this base | HIR implication |
|---|---|---|
| `FrozenRef`, `FrozenArena`, `frozen_arena` | No definitions/references found in scoped compiler, library and owned runtime search | Names in the governing plan are proposals, not usable admitted primitives |
| `HirModule`, `SymbolTable`, `Scope`, `HirSymbol` in `20.hir/hir_types.spl` | HIR contains mutable dictionaries/lists; SymbolTable is a class; Scope has its own mutable binding dictionary | A wrapper or copied top-level record cannot establish deep immutability |
| `SymbolTable.module_snapshot()` | Explicitly moves container references into another class; comments rely on subsequent lowerer reset to replace its fields | This is a lifetime/ownership handoff assumption, not a deep clone or freeze API |
| `nogc_async_immut/persistent_map` | Concrete HAMT `get/set/remove`; set returns a new map and helper operations rebuild changed child arrays | Candidate persistent topology; values/keys remain dynamic references, so nested HIR payloads are not frozen |
| `nogc_async_immut/persistent_vec` | Concrete RRB implementation and persistent API exist | Candidate collection representation; native semantics and nested alias isolation remain unverified here |
| Persistent map/vector transient builders | `_frozen` bit makes later builder methods no-ops; vector `build()` returns its raw `_items` array | Method-level discipline, not revocation of existing aliases or sealed storage; do not equate with P1 freeze |
| `common/bytes/span.spl` | `ByteBuffer.freeze()` constructs ByteSpan over `self.buf`; mutable builder remains available | Read-view facade over shared storage, not ownership-consuming deep freeze |
| `nogc_sync_mut/mem/gen_arena.spl` | GenHandle(index,generation), mutable slots/generations/live/free lists, stale-handle checks | Useful identity/reuse pattern; does not provide frozen arena publication or reader lifetime pins |
| `common/structural/transfer/transfer_contracts.spl` | FrozenShare/OwnedMove/ScopedLoan vocabulary and envelope validation; header explicitly says semantic/wire contract only | Reuse terminology and invariants, not an assumed runtime implementation |
| `55.borrow/borrow_check/mod.spl` | TransferOut records move for consuming modes; FreezeRegion records use; AcquireSnapshot records use/assign/loan-copy | Static bookkeeping exists; FreezeRegion does not itself prove alias revocation |
| LLVM `core_codegen.spl:1261` onward | TransferOut, TransferIn, FreezeRegion, AcquireSnapshot and CommitUpdates emit explicit unsupported panics | Current LLVM path cannot execute the proposed generic freeze/share/transfer primitives |
| Native x86 instruction selector | FreezeRegion and AcquireSnapshot route to unsupported-instruction diagnostics | No alternative native proof for these operations from this path |

## Publication ordering and lifetime pins

`nogc_sync_mut/atomic.spl` defines Acquire/Release/AcqRel/SeqCst vocabulary.
AtomicI64 operations forward to runtime handle APIs without forwarding their
ordering argument. The inspected `runtime_native.c` load/store/CAS bodies use
C `memory_order_seq_cst`, a concrete implementation rather than a no-op.
However, an atomic integer alone does not make a shared HIR graph immutable,
bind an epoch to its storage, or keep it alive after eviction. A future owner
must define the ready-handle publication, acquisition and reclamation protocol.

`nogc_async_immut/atom/__init__.spl` must not be treated as an established
lock-free graph publication primitive: `deref()` reads `_values[0]`, and the
inspected `swap()` reads/writes that slot then increments an atomic version.
The comments discuss CAS, but that body does not atomically exchange the
payload and version together. No concurrent safety qualification was run.

`compiler/00.common/cache_contract/direct_read_pin_v1.spl` provides a pin record
with process/boot/epoch/manifest identity and a time-validity predicate. The
library `common/cache_host_authority_v1.spl` exposes begin/validate/renew/open/
release pin FFI wrappers. In inspected `runtime_cache_host_authority_v1.c`,
reader-pin functions are explicitly unsupported (`return -1`) in the Windows
UNSUPPORTED block and in the other inspected implementation block. These
interfaces are not available proof of HIR heap pinning. Even a completed CAS
filesystem pin would need an explicit mapping/lifetime link to the HIR owner.

`nogc_sync_mut/rt_hal/process_task_arena.spl` is a bounded process-task adapter
with capabilities and unavailable-provider functions. Its task generation and
cancel/reap machinery is not a frozen memory arena. Do not substitute process
containment or a result receipt for in-process pointer lifetime protection.

## Typed identities and feasible PR-A boundary

Existing nominal records such as SymbolId, ScopeId, GenHandle and
`PersistentExtensionId` demonstrate implementable wrapper types. The latter
uses canonical structured identity and treats its hash as an index, not the
collision authority. They support introducing names such as HirSnapshotId and
region/node identity without changing HIR layout. An identity is not a pin,
an ownership token, or proof that two runtime targets are equal.

PR-A can remain preparatory and behavior-preserving:

1. Add nominal identity declarations and read-only interface vocabulary with
   an explicit *unfrozen/preparatory* contract. Keep existing lowering routes.
2. Inventory every raw reader/constructor and classify returned data: scalar
   copy, immutable text, borrowed semantic reference, mutable owner or handle.
3. Avoid returning raw mutable HirModule/SymbolTable/Dict/list aliases from a
   facade advertised as immutable. If compatibility requires such exposure,
   label it as borrowed legacy access and do not admit it as a frozen snapshot.
4. Add compile-time misuse fixtures only once actual visibility/ownership
   enforcement is demonstrated by the admitted compiler; naming a field
   “private” or a wrapper “FrozenRef” is insufficient.

PR-A cannot claim P1 completed, publish a reusable frozen snapshot, enable
concurrent target readers, remove existing raw entrypoints, or use unsupported
FreezeRegion/AcquireSnapshot MIR as a working mechanism. P1 needs an actual
owner/seal design that closes nested aliases, invalidates builder mutation,
and establishes reclamation and failure/cancellation cleanup.

## Validation assets and remaining evidence

Relevant source fixtures exist under
`test/01_unit/common/structural/transfer_contract_spec.spl`,
`test/01_unit/common/structural/parallel_commit_contract_spec.spl`,
`test/01_unit/app/interpreter/persistent_vec_spec.spl`, and
`test/01_unit/std/complete/atomic_*_complete_spec.spl`.
Their names or stored summaries do not qualify frozen HIR on this revision.

Required future evidence: nested-reference mutation refusal; builder aliases
invalid after freeze/move; persistent updates preserving old payload graphs;
reader acquire/release and eviction races; stale generation rejection;
cancelled/failed publication exposing no ready handle; backend parity for any
new MIR freeze primitives; and actual admitted native execution. CPU/RSS
baseline collection belongs to the campaign owner and was not performed by
this read-only inventory lane.
