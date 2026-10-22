# Actual mono archive function consumer

This change executes the existing mono rewrite and specialization consumers
against complete owned-scope HIR cache decodes. It implements one root or one
FIFO specialization transaction and exact publication into compact resident
state. The production driver still selects the retained pass. This is not a
full CLI RSS repair: original promoted HIR, the original compatibility collector,
module assembly, remaining validators, and MIR owners have not been replaced.

## Actual consumer and authority

`40.mono/mono_archive_types_v1.spl` projects signatures as name, parameter types,
return type and type parameters. It never retains `HirParam.default`, full
functions, expression bodies or symbol tables. A template recipe records the
original defining module/SymbolId and the exact parameter canonicalization used
by the existing ordinary function and inherent-method collector. The retained
collector now uses that same recipe helper; its default mode remains `Retained`.

The actual inference implementations are shared: public full-function inference
methods delegate to the same signature implementations used by archived calls.
Actual call and generic-method rewriting use those signature accessors. In
`ArchiveRequests` mode the existing request allocator retains compact signature
and typed FIFO records rather than specializing or registering full template
bodies. The same structural mangling, display collision, depth limit, SymbolId
allocation, return-name facts, diagnostics and statistics remain in that code.

`40.mono/mono_archive_state_v1.spl` defines compact facts, resident FIFO state and
an explicit publication delta. The compatibility factory reads the actual
unrewritten collector. Eighteen declaration maps, exact module+SymbolId ownership
strings and template recipes/signatures are projected; no fake provider module
graph is constructed. Sixteen maps are borrowed read-only by body consumers.
The mutable return/name, specialization display/signature, once and unresolved
indexes are copied into scratch, with only new typed rows escaping in the delta.
This factory does not free the original collector or provide an owned producer
for those compact facts.

`80.driver/cache/hir_mono_archive_consumer_v1.spl` admits complete existing
`HirBodyArchiveV1` descriptors with one selected closure, producer header and
runtime/provider authority. Existing file-backed descriptor checks recompute
source/cache identities and selected runtime receipt bytes. Admission additionally
requires exact collector inventory and paths. Every visit rechecks authority,
state digest and the feature policy before decoding the complete selected body.
A queued visit checks the original function, recipe, canonical signature and
specialized signature before running the actual specialization and rewrite code.

The immutable output stage is **`mono-function-rewrite-v1`**: the output is a
complete cache module container, but only the identified function is transformed.
It is not a final post-mono module. Original templates remain in that intermediate
container. Source/closure/producer/runtime/stage, input body/warning hashes, output
complete-module/function hashes, predecessor state and exact delta hash bind its
key. Input admission deliberately remains `lowered-unresolved-v1`; this fixture
seam cannot stand in for the real resolved/advice-transformed production input.

Publication validation owns another scope and checks the complete stored output,
epoch/cursor, actual typed request/signature rows and seals. New requests are
replayed through the **same actual allocator** to verify concrete type/depth,
structural mangling, display collision and defining-module selection. It closes
scratch before publishing already-promoted rows and scalar counters. Missing,
corrupt, mismatched, stale or nested transactions refuse without resident mutation.
Warning aliases are cleared and the dynamic cache diagnostic owner is promoted;
pause/promotion/end failures terminate rather than allowing scratch escape.

## Native acceptance fixture and present evidence

`test/fixtures/compiler/hir_mono_archive/main.spl` contains 29 positive guarded
checks. It parses actual complete source fixtures and stores complete codec bodies,
not signature-only providers. The imported native provider returns 43 for integer
and text specializations before and after scope closure. The actual archive
consumer reads that provider body and compares every generated complete function
digest against the retained pass; decoded leaf values, nested call names, owner
symbol rows and counters are inspected while their scope lives.

Controls include repeated dependencies, two distinct type instances, recursive
deduplication, polymorphic recursion/depth and diagnostic parity, exactly-once
E-MONO-040 across repeated leases, table-local SymbolId collision and last
declaration selection versus the retained pass, body/signature mismatch, corrupt
output, altered delta/stage, wrong closure, nested-scope refusal and descriptors
read after a second allocation scope. A promoted signature is projected from a
scratch parameter with an executable default; its declared schema excludes that
body family entirely. Request-only state is not an emission/pruning receipt.

The existing canonical fixture launcher accepts only whitelisted `typecheck`
(default, 31 checks) or `mono` (29 checks), selected by
`SIMPLE_HIR_LEASE_FIXTURE_KIND`. It retains actual admission/runtime capsule,
source/config/fixture/control hashes, clean-or-exact-receipted alias ownership,
private cache and cap/timeout checks. For mono it clears ambient diagnostic policy
so the fixture tests production defaults. No seed or interpreter fallback exists.

Static evidence is in the external
`C:/dev/simple-phase3-bootstrap-evidence/hir-mono-archive-static/source-audit.json`:
three shared inference bodies match their prior implementations apart from the
type-only projection/accessor change; a 61-method actual rewrite call closure
does not reach aggregate collection/drain/pruning; no write to the 16 borrowed
declaration maps appears in that closure; compact signature excludes full body
owners; the fixture has exactly 29 guarded check increments. This is source
analysis, not a Simple parser/typecheck or native execution result. Working and
staged direct-env guards, diff checks and launcher shell syntax are required.
**Native compilation/execution and RSS/time improvement are unmeasured.**

## Next production route and reclamation dependencies

The full qualified CLI still must pass its unchanged physical source inventory,
typechecks, validators and RSS cap. The finite production dependency order is:

1. Extend the actual owned `lower_streaming_hir_shard_transaction_v1` transaction
   in `driver_hir_pipeline_lowering.spl`, which already lowers/decodes and writes
   complete HIR then clears module-local/flat roots, to return typed immutable
   archive and declaration/registration receipts. Its current `i64` compatibility
   entry can remain default until the full route is ready. Do not enter the
   nested owning `hir_body_archive_store_v1` inside that scope; extract a shared
   borrowed-scope store primitive used by both owners.
2. Produce compact mono registration through the **actual ordered collector**.
   Independent per-module dictionary merging is incorrect: duplicate template
   selection, generic-method rejection of earlier keys and ambiguous nominal
   names depend on previous modules. A scratch collector must read prior compact
   authority, publish exact new/updated rows and root order, then mutate resident
   summary indexes only after scope end. Full generic functions and original
   SymbolTables must never enter that resident owner. This is the next mono seam.
3. Admit semantic archive stages after existing quiet method resolution and
   advice/aspect transforms, binding prior artifact, exact semantic pass receipts
   and policy to the same producer/source/full-closure/runtime authority. Preserve
   HM, safety, Any, enum, value layout, effect and criticality checks and their
   severity, diagnostic order, counters and pass receipts.
4. Rewrite roots in the retained route's module-key/ascending-symbol order, with
   a root-phase barrier before FIFO drain. Assemble each final module from exact
   rewritten root and emitted specialization descriptors; missing coverage must
   refuse. Set owner SymbolId counters against the final global counter and prune
   only templates with actual emitted bodies and the original unresolved policy.
   Run every existing `post_mono_verify_modules` check under unchanged strictness
   on the actual final archived modules, aggregating the same order/counters.
5. Supply complete provider/generic bodies to the actual MIR consumer through
   scoped archive access; declaration/layout/global summaries remain resident.
   Only then replace full module promotion in
   `lower_streaming_surface_source`/`lower_retained_surface_module`, stop storing
   full graphs in `lowered_by_surface`, `phase_hir_modules` and entry/flat owners,
   and qualify the unchanged full CLI under the cap. Dropping references to
   already-promoted graphs cannot reclaim their no-GC allocations.

The driver authority/typed transaction owner and mono registration owner can be
implemented independently with these shared receipt/scope boundaries. No partial
production activation is justified by this consumer fixture alone.
