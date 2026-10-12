# Ordered archive-backed mono registration producer

This follow-up replaces the retained full collector prerequisite for the explicit
mono archive consumer with an actual complete-body registration producer. It
does not activate the production driver or implement the root/FIFO barrier,
final module assembly, remaining validators or MIR leases. Full CLI RSS acceptance
remains outstanding; no reclamation or performance improvement is measured.

## Shared actual collector and exact publication

`MonomorphizationPass.collect_declared_globals` and `collect_generics` remain the
actual collector. In its explicit `ArchiveRequests` mode, canonical function and
inherent-method bodies exist only in scratch; resident facts receive signatures
and recipes. Generic structs/classes retain their existing compact field/type
facts and counters, with no full definitions or engine templates registered.
SymbolTables are consumed while their module is available and projected to exact
module+SymbolId ownership strings. Retained mode keeps its existing full owners
and engine registration behavior.

`compiler.mono.mono_archive_registration_v1` exports these concrete interfaces:

- `mono_archive_registration_create_v1() -> Result<MonoArchiveRegistrationOwnerV1, text>`
  requires inactive scope and initializes persistent cache identity before scratch.
- `mono_archive_collect_registration_in_owned_scope_v1(owner, module, module_name, archive)`
  returns a typed `MonoArchiveRegistrationReceiptV1` in the parent's active scope.
  It requires the real runtime state query to return 1, exact complete body/source
  admission and the selected closure/producer/runtime authority of earlier modules.
  It never begins, pauses, promotes or ends the borrowed parent scope.
- `mono_archive_publish_registration_v1(owner, receipt) -> Result<bool, text>`
  verifies in its own scope and changes resident indexes only after that scope ends.
- `mono_archive_registration_seal_v1(owner, expected_inventory)`
  returns the existing `MonoArchiveAdmissionV1` only for exact admitted module
  names/path coverage and revalidated complete archive repository authority.

The owner has one compact `MonoArchiveStateV1`, archive descriptors, ordered
per-module root SymbolId lists, three generic declaration counters, epoch and seal
state. Expected inventory must come from the already admitted driver inventory;
the names/path map is a coverage check, not fabricated source authority.

The receipt contains actual archive authority, predecessor digest/epoch, changed
rows, sorted non-template root IDs, next SymbolId, declaration counters and seal.
Its 21 typed row variants cover all 18 declaration dictionaries plus canonical
template signatures, recipes and symbol ownership. They admit text, booleans,
exact HirTypes, type parameters, text arrays, signatures and recipes, with no full
HirModule, HirFunction, HirParam, expression default, class/struct body or SymbolTable.
Absent type presence and full codec type metadata are sealed explicitly.

Capture clones compact dictionary indexes into scratch, preserving previous
declarations for the same actual collector. It emits only added/changed typed
rows. This preserves cross-module template overwrite, generic-method rejection
of earlier keys, repeated generic type identity and ambiguous nominal names;
independent per-module dictionary merging would not. Dictionary snapshots,
the scratch collector and full decoded module never enter publication.

Publication rejects stale, occupied, partial, changed-body or changed-authority
transactions. It decodes the actual complete archive and reruns the same collector
against the same predecessor to verify the exact row/root/counter seal. After
pause/cache diagnostic promotion/alias clearing/end, only previously promoted row
payloads update the existing resident dictionaries; ordered roots/archive/scalars
advance once. Failed verification changes no resident epoch or index.
Sealing promotes only the verified repository authority digest and freezes further
registration. The same explicit body consumer can then use these actual produced
facts with no persistent original collector requirement.

## Driver ownership boundary

The driver-owned typed transaction adapter under development uses the actual
`lower_streaming_hir_shard_transaction_v1` scope. After complete body archive
publication, it calls borrowed registration capture, pauses and promotes its typed
transaction receipt plus existing diagnostics/ABI/cache/memo/frontend owners,
resets module-local lowerer roots and rolls back flat module rows, then ends the
parent scope. Registration publication must occur outside that parent scope.
The compatibility `i64` route stays default until all production consumers agree.

Actual runtime/std or environment-variant admitted authority must select the
input descriptor. Cache/source/producer/runtime/stage digests do not establish
authority merely because they have a valid length. Input remains
`lowered-unresolved-v1`; later semantic stage admission must still preserve the
real resolution/advice/validator sequence before production mono.

The new real state query is dependency
`8f87fa0eb6ee9c1df51c487e0a0775152e9061ca`, exposed as
`std.nogc_sync_mut.sffi.runtime.transient_array_scope_state_v1() -> i64`.
States 0/1/2 are inactive/active-unpaused/active-paused. It reads actual owner state
without changing it and does not grant ownership of another caller's lease.

## Acceptance and remaining limits

The actual native mono fixture now has **47** guarded checks. Its original 29
consumer controls remain, with 18 registration controls for inactive and paused
capture, nested publication, stable receipt reads after close, stale/duplicate
publication, forged row metadata, incomplete inventory, exact produced facts and
statistics versus the retained collector, ordered roots, cross-module collisions
and nominal ambiguity, sealed refusal, and real FIFO body parity using the new
producer. The clean or exactly receipted canonical launcher `mono` selector now
requires the 47-check output; its `typecheck` branch remains independent.

Native compilation/execution are pending root serialization. Source contracts,
guard count, working/staged direct-env checks, diff and launcher syntax can be
verified without jobs; they are not substitutes for native ownership evidence.
Per-module collection validation runs the actual collector twice and clones
compact indexes only in scratch; CPU/time/RSS impact is unmeasured. Persistent
summary payloads still occupy no-GC memory, including changed declaration rows.
Their size is not established by counting row variants.

Next required production work is the ordered root barrier and complete FIFO drain,
immutable final module assembly and full post-mono validators, followed by
complete MIR provider body leases. Only after those owners are sound may the
driver remove full HIR promotion and resident body maps and qualify the unchanged
full CLI inventory under the original cap. Existing already-promoted HIR cannot
be reclaimed by clearing its references.

The seal requires expected_order: [text] from the admitted driver schedule,
including exact length, membership, absence of duplicates and equality with the
owner's published root-module sequence. Complete names/paths alone cannot prove
collision precedence. Native negative guards now cover reversed full order,
a duplicate-name order and a truncated order; all refuse without sealing or
advancing the owner. These guards remain unexecuted pending the native slot.

Selected-provider input dependency `f7c60c79a8dc8187121c4f6357559c75e218eba1`
adds the actual admitted bundle/target/backend selection digest and exact per-source
authored/content identity. Registration and repository formation require identical
provider selection and receipt path across modules, alongside closure, producer
and runtime digest. Repository v2 binds both selection and receipt path. Per-source
authored/content identities remain distinct, covered by each archive input key;
they must never be compared globally. Native dependency fixtures cover changed
provider keys and descriptor/source mismatches; execution is still pending.

Two further actual mono fixture controls independently store complete archives
with different selection digests, or the same digest and a distinct receipt path
containing the actual canonical receipt's exact bytes. Each descriptor must pass
individual source/body/input validation before the cross-module registration and
repository refusal is tested. Both refusals preserve the first module's published
epoch and coverage. The selection strings are explicit consistency controls, not
fabricated production admission; the real canonical capsule remains bound and
verified by the launcher. Combined with the ordered execution controls the mono
launcher includes these two consistency checks. With the subsequent schedule-proof controls it requires 71 checks. Native compilation/execution remain pending.
