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

The native fixture launcher's `cold` selector requires a replayed canonical
Stage2 admission whose tool snapshot already contains the actual managed-tool
projection. It replays the six sealed tool environment assignments as data and
hands the exact admitted tool/snapshot paths and digests to the fresh fixture.
Compilation retains the published capsule; cold selection consumes the distinct
original runtime root and snapshot named by that admission. Both authorities
remain in the evidence. The old frozen producer and attempt7 tool snapshots do
not contain a managed projection, so they cannot qualify the seven-check cold
control. Refusal is pending evidence, not a zero-check success.

The original archive now has one guarded complete-body borrowed reader shared
by the typecheck and semantic adapters. Four appended native guards preserve
the original 47 and exercise inactive/paused refusal, actual decoded body and
function contents, and a forged body seal (51 total). These guards remain
unexecuted. The semantic adapter extracts the existing safety, Any-origin and
enum-declaration checks into read-only per-module diagnostic collectors;
retained wrappers keep the same module iteration and aggregate pass receipts.
Actual checker implementation files have no module-level mutable memo roots;
only rendered text, cache diagnostic ownership and scalar/archive identity
escape the semantic lease. The native semantic control has 21 guards including
actual unsafe assembly/Any/duplicate-discriminant findings, clean neighbors,
advisory/warn/deny behavior, two-module pass-major publication, reversed-order
refusal before publication, foreign scope refusal, and a failed-stage replay.
No native result has been collected. Semantic publication does not admit value
layouts, collection analysis, quiet resolution, cold publication witnesses,
monomorphization/post-mono validation or MIR. Those owner adapters remain
mandatory before the bounded production loop can be selected.

Publication now verifies the complete captured output seal and re-executes the
actual archived semantic consumers before accepting any diagnostics. A caller
cannot clear deny-channel errors or construct a forged clean receipt with a
new self-consistent digest: both are compared against independently recollected
actual output before any context mutation. The two new native guards reach
publication with those corruptions, require untouched context warnings/errors,
and preserve closed scope ownership. The shared read-only verifier is available
to the eventual final repository owner; it grants only semantic output parity,
not the missing driver prerequisite and post-mono admission.
