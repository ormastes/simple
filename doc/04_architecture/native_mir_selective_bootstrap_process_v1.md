# Retained HIR bootstrap object processes v1

<!-- codex-architecture -->

Status: implementation design approved by independent Astra review; source and executable acceptance remain UNRUN. Base: `83be266ace4`. This is a future lineage only; frozen campaigns remain immutable.

## Decision and boundary

Extend the existing selective retained-HIR producer, physical-emission manifest, worker and `run_ledger_shards` process scheduler for the canonical Cranelift backend. Do not add a MIR codec, scheduler, seed, runtime fork, or LLVM-only substitute. Each child decodes its own complete retained HIR body and bounded declaration/registry summaries, lowers and emits one physical object with the existing selected provider. Source frontend fallback is forbidden.

The existing selective ordinary-entry route stays unchanged. A bootstrap route is admitted only after all actual bootstrap context owners have exported and imported equivalent state. Nonempty unsupported resource/HAL, typed storage/evidence, coverage/MC/DC, demand/archive/collection and native-group state remains refused. SOURCE mode remains refused until existing seal ownership is preserved. No guard is removed merely because an environment flag requests parallelism.

## Frozen interfaces

B owns `src/compiler/80.driver/driver_build/native_mir_selective_bootstrap_context_v1.spl` and its new unit acceptance spec. No existing source file is edited by B.

`NativeMirSelectiveBootstrapOwnerReceiptV1(kind: text, digest: text, bytes: i64, rows: i64)` has exactly three ordered kinds: `function_registry`, `callable_registry`, `enum_composite`. Each digest is lowercase SHA256, each body is positive and at most 64 MiB, each row count is 0..1,000,000; total snapshot bytes are at most 128 MiB. These are hard format bounds, not permission to exceed admitted tree/phase/disk limits.

`NativeMirSelectiveBootstrapContextV1(source_identity: text, context_identity: text, physical_manifest_identity: text, producer_identity: text, backend: text, target: text, entry_owner: text, entry_source: text, stage4: bool, skip_post_chain: bool, owners: [NativeMirSelectiveBootstrapOwnerReceiptV1])`.

All four identities are exact lowercase SHA256. Backend is `cranelift`, `llvm`, or `llvm-lib`; target is explicit, not inferred from the host. The bootstrap entry owner is `app.cli.bootstrap_main`; source is its canonical repository-relative path. `skip_post_chain` equals `not stage4`, preserving the existing serial bootstrap policy. Physical manifest identity binds actual mono aliases, specialization placements, source/provider/emission orders, and retained HIR/declaration digests.

B APIs:

- `native_mir_selective_bootstrap_validate_v1(context) -> text`: empty only for a well-formed supported context.
- `native_mir_selective_bootstrap_encode_v1(context) -> Result<text, text>`: bounded canonical SDN, schema `simple/mir-selective-bootstrap-context/v1`.
- `native_mir_selective_bootstrap_decode_v1(blob, expected_source, expected_context, expected_physical_manifest, expected_producer) -> Result<NativeMirSelectiveBootstrapContextV1, text>`: reject unknown/noncanonical/trailing input, wrong identity or owner bounds.

The existing export directory contains `bootstrap-context.sdn` and `bootstrap-owner-function_registry.sdn`, `bootstrap-owner-callable_registry.sdn`, `bootstrap-owner-enum_composite.sdn`. The single post-mono producer writes owner files first, validates readback/digests and budgets, then atomically publishes the context. The physical manifest is published last and must bind the context digest in its versioned bootstrap extension. No environment path alone grants authority.

The context source/context identity comes from the existing selective bundle source and `driver_mir_selective_context_identity_v1`. Producer identity is SHA256 of the exact existing `hir_owned_artifact_context_v1().producer_header`. Physical identity is the exact bootstrap physical manifest digest, excluding its context-digest seal field to avoid a circular digest. Both directions explicitly bind the same immutable generation.

A owns exact owner-specific export/import implementation and equivalence evidence in `mir_data.spl`, `bootstrap_globals.spl` and declaration/prescan owners. Shared proposed entry names: `bootstrap_fn_registry_snapshot_export_v1` / `bootstrap_fn_registry_snapshot_import_v1`, `bootstrap_callable_registry_snapshot_export_v1` / `bootstrap_callable_registry_snapshot_import_v1`, `bootstrap_enum_composite_snapshot_export_v1` / `bootstrap_enum_composite_snapshot_import_v1`. Owner modules may refine signatures in coordination with C; they must return actual bounded snapshots/validated installed state, never success placeholders. Export actual post-mono function/default/shadowing/type and callable/static metadata. Do not serialize full MIR functions. Include builtin identity and actual enum/composite prescan order. Imported state must have a verified equivalence digest before bootstrap lowering is enabled.

C owns worker/eligibility wiring. Consume the context and A owner imports only after retained bundle/context/producer identities match, then use the exact native-bootstrap entry and post-chain semantics. Ordinary explicit-native semantic policy must not silently substitute for bootstrap semantics. Preserve existing mono alias/specialization placement admission, actual entry MIR ownership, unsupported-state guards and error diagnostics.

D owns private writable caches and parent adoption through the existing process owner. `SIMPLE_NATIVE_BUILD_CACHE_DIR` is invocation/generation/worker-private; shared retained frontend/HIR/declaration inputs are read-only. Each worker writes only its owned fragment/object/log/claim. Parent reads validated fragments and updates its canonical partial-result ledger and shared cache once in original manifest order. Existing `native_mir_shard_link_inputs_v1` remains an all-PASS exact-inventory gate; any original HIR failure, excluded/blocked source, child failure, timeout or missing result forbids linking. D selects existing cache validation/receipt APIs after checking their actual contracts; B does not create a competing cache API. D coordinates any `native_build_main.spl` edits with the root frontend-fallback lane.

## Complete partial inventory

Keep the complete original source inventory. Each original logical row has a source digest, physical emission owner, dependency names, and exactly one state: `READY`, `HIR_FAILED`, `EXCLUDED`, `BLOCKED`. Only READY emissions with complete admitted retained bodies and declarations enter the worker queue. READY may depend only on READY providers; absent, failed or blocked dependencies refuse readiness. Retain original diagnostic ownership for non-ready rows. Deduplicate physical emission jobs without dropping logical rows. The original aggregate failure remains failure while independent READY objects finish and remain reusable. Partial bundle support requires a versioned manifest extension; never silently delete failed rows from the old all-provider format.

## Admission and acceptance

Resolve actual `--jobs`/`-j`/`--threads` through the existing request owner. Admit worker count against measured parent, exporter, per-worker body/MIR/backend/tool-process-tree RSS, phase/tree memory and disk reserves. Metadata, pending receipts and retained IR/body storage count toward those budgets. No all-module IR staging or unbounded pending body heap is allowed. Ten admitted jobs means ten real worker processes, not backend argv 10. An insufficient budget is explicit and never disables enforcement.

Acceptance uses the existing Simple unit/system runner and `native_mir_selective_process_spec.spl`, qualified self-hosted CLI/provider/runtime only. Required evidence: canonical Cranelift with at least twelve real physical emissions reaches actual peak overlap >=10 with requested/admitted 10 and never exceeds 10; long/short slot refill; jobs1 semantic/object set equivalence; unique writable worker roots; exact owner round-trip and serial-prescan equivalence; stale/wrong snapshots rejected; partial HIR plus multiple independent compile failures finish with a complete ordered failed ledger and no link; timeout/SIGKILL/cancel drains/reaps owned descendants; no source frontend fallback. Source/spec authored without a qualified CLI is UNRUN, not PASS.

## Ownership and review

A: `/root/c4_cranelift_rodata_relocation`; B and acceptance coordination: `/root/module_collection_slot_refill`; C: `/root/provisional_nested_session_fix`; D: `/root/runner_sdn_bytes_fix`. Lower-model sidecars: N/A. Merge owner: root. Exact final normal/highest-capability reviewer: `/root/astra_c4_integration_review`. Shared interface changes must be communicated before implementation. At most six verify/fix cycles, and no unchanged green reruns.
