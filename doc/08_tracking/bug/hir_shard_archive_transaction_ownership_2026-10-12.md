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
