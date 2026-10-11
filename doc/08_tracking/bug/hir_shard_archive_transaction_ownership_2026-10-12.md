# HIR shard archive transaction ownership

Status: inactive prerequisite authored; native qualification pending.

The streaming shard transaction returned only an integer. Its complete decoded
or lowered `HirModule` was intentionally discarded before scratch reclamation,
so a bounded consumer could not identify the exact durable body or publish the
same ordered monomorphization declarations afterwards. Returning that module
would retain its functions and symbol tables and defeat the memory boundary.
The owning archive writer also promoted only four successful descriptor strings,
although descriptor inputs and dynamic failure reasons can be scratch objects.

`lower_streaming_hir_archived_shard_transaction_v1` is an explicit, inactive
typed adapter. The existing integer method and all production callers remain
the default. The adapter derives `HirBodyArchiveInputV1` with the actual selected
compiler file identity, current cache header, frozen surface closure, exact
physical source bytes, and an existing RuntimeStd V2 sealed CAS admission.
Matching bytes at a caller-selected receipt path do not constitute admission.
Only `lowered-unresolved-v1` bodies are stored.

Within the original HIR scope, parsing/lowering/cache publication precede the
borrowed archive writer and the shared ordered declaration collector. The latter
returns the actual compact registration delta bound to that archive; it does not
merge independently collected per-module dictionaries. The existing diagnostic,
ABI, 49 phase memo roots, frontend registry roots, and reverse-reference ordering
remain intact. Cache diagnostic ownership, the whole archive descriptor and the
compact registration receipt are additional explicit escape roots. Flat HIR rows
are rolled back and module-local lowerer owners reset before reclamation. No
`HirModule`, function block, or symbol table is a new promoted result. A caller
must publish registration **after** this transaction returns, in the original
module order. No main loop is switched by this change.

The borrowed writer checks actual runtime scope state: active/unpaused is
required; inactive and paused callers are refused without acquiring, pausing,
promoting, or ending another caller's scope. Its owning wrapper promotes the
complete `Result`, including descriptor inputs and failure text.

Regression sources:

- `test/fixtures/compiler/hir_body_typecheck_lease/main.spl` preserves all 31
  existing checks and adds 12 real borrowed-scope, refusal, caller-lifecycle,
  post-close descriptor and fresh-consumer checks. The exact admission launcher
  now requires 43; the separate mono fixture remains 44.
- `test/01_unit/compiler/cache/driver_hir_archive_authority_spec.spl` rejects
  foreign producers, matching but unadmitted receipt bytes, and occupied leases.
- `test/01_unit/compiler/cache/driver_hir_shard_transaction_spec.spl` invokes the
  real parser/driver seam, verifies rollback on malformed source, preserved
  diagnostics after subsequent scratch reclamation, and fresh/cache-hit durable
  transactions without context body retention.

These tests are authored, not executed. Native scope-state and archive lifecycle
qualification, complete compact consumer handoff, publication/order coverage,
eventual main-loop selection and actual full-CLI RSS evidence are still required.
The explicit RuntimeStd selection is not yet supplied by production orchestration.
Environment variants need their real selected BuildPlan/publication through
`environment_variant_provider_receipt_v1`; arbitrary environment paths or hashes
cannot replace that missing typed authority handoff. Coverage-rewritten source
content also needs its actual physical-source authority before this byte-exact
adapter can be selected.

Follow-up source authority binds the selected provider independently of its
runtime snapshot/receipt bytes. Additive strict fields carry the actual normalized
source body digest and authored path. The driver replays the same reserved
coverage-wrapper owner as source loading against the real physical file, and
the archive input key rechecks that binding. Four further native guards preserve
the original 43 and require distinct provider selection keys, exact descriptor
matching, and refusal of altered source-body identity (47 total). They remain
unexecuted until the actual native launcher is authorized.

The managed cold native path now captures a compact selection from
`native_runtime_authority_v1`, the existing linker authority. It admits the
canonical managed tool owner, snapshot `NativePinnedArtifactV1`, and every
archive chosen by the unchanged central bundle/platform selector. This snapshot
owner already decodes at most 64 MiB; its admitted snapshot is the archive's
runtime authority file, which explains that separate receipt read bound.
RuntimeStd V2 retains its canonical owner's independent 4096-byte bound.
The selection seals the actual compiler, backend, target or host default,
platform archive format, explicit bundle, snapshot path/digest and ordered pins.
Per-module admission re-projects the current exact set from that live owner;
terminal hashing remains available through the existing runtime validator.
Production native orchestration captures this before HIR and a selected shard
adapter consumes the retained selection. It does not select the bounded loop.
Generated runtime objects (`runtime_path=none`) retain their distinct existing
object-compilation authority and are not reclassified as archive providers.
Warm RuntimeStd and live environment publication handoffs remain outstanding.

Cold owner initialization must precede the projection scratch lease. The actual
core-C runtime accepts heap promotion only while the owning scope is paused.
Tool admission now builds its complete projection in an owned lease, promotes
the full result after pause, closes, then publishes global bindings/identity and
environment. Runtime snapshot and late selected-file admissions follow the same
protocol with newly built replacement arrays; they cannot mutate a persistent
registry with unpromoted aliases. First admission inside a foreign active or
paused lease is refused. Generated-object binding uses its own identical
pause/promote/close-before-publication protocol. Ownership failure panics rather
than publishing partially retained roots. The fresh-process
`hir_managed_runtime_cold/main.spl` control has seven guards for genuinely cold
owners, active/paused refusals, actual file admission, post-close revalidation and
stable repeated selection. The generated runtime mutation control also checks
occupied-lease refusal and ownership release. These controls are not executed.
