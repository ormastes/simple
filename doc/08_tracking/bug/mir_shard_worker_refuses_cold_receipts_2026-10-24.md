# MIR shard worker and link child refuse eligibility on cold-HIR receipts (2026-10-24)

## Symptom
Phase-3 native-build of `src/app/cli/bootstrap_main.spl` never runs MIR in parallel; every
worker exits 1 and the build falls back to in-process MIR (~100h, see
`self_hosted_mir_lowering_pathologically_slow_2026_10_22.md`):

```
[mir-shard] eligibility refused lane_ok=false lane_reason='output format re-reads MIR set' ... receipts=1471
```
and the bootstrap-flat variant (same line, different lane_reason). Dynload maps the worker to
`OutputFormat.Both` (`src/app/io/_CliCompile/compile_targets.spl:1583-1587`), which makes the
staged lane ineligible when SIMPLE_BOOTSTRAP is set; with `--mode one-binary` and
SIMPLE_BOOTSTRAP unset lane_ok is true but `receipts=1471` still refuses.

## Root cause
`native_mir_shard_eligible_v1` (`src/compiler/80.driver/driver_aot_pipeline.spl`) requires
`cold_hir_typed_receipts.len()==0`. `capture_cold_hir_typed_receipts_v1`
(`driver_hir_pipeline_lowering.spl:330`) always runs cold in the bootstrap CLI (package-index
markers never published), so receipts are always non-empty. The same check gates the MIR link
child (`aot_link_mir_shards_v1`).

## Readers audited
Receipts/object maps are read after MIR only by cold object persistence:
`driver_aot_native_output.spl:1166-1219` (record/persist; persist called at :3232 before
link), full-index paths gated on `runtime_std_full_inventory_selection` (:3915, :4204,
`driver_aot_pipeline.spl:248`, `driver_pipeline_lowering.spl:550,879`), and cold_full_index
producers. Workers publish objects/ledger via `native_mir_shard_publish_pass_v1` and need none
of it; the link child re-admits objects from the ledger (never recording them), so persist
would see 1471 receipts and no object paths.

## Fix (replaces the workaround; 2026-10-24)
Sharding and cold persistence now compose; the receipts requirement and
`mir_shard_drop_cold_receipts_v1` are gone.
- Eligibility no longer looks at `cold_hir_typed_receipts`.
- Workers keep the receipts, so `compile_to_native` records each claimed module's capsule
  identity as usual. A worker never persists (`shard_queue != ""` skips
  `driver_cold_hir_persist_verified_objects_v1`: it holds only its claimed objects).
- `native_mir_shard_publish_pass_v1` writes the capsule identity as a 4th sidecar line
  (sidecar is now 5 lines); `NativeMirShardLinkInputsV1` gains `capsule_identities` and
  `objectless_modules`.
- The link child replays objects/objectless modules from the ledger through
  `driver_cold_hir_record_verified_object_v1` / `_record_objectless_v1`, then the ordinary
  persist at `driver_aot_native_output.spl` runs once over the full inventory.
Spec: `test/01_unit/compiler/driver/native_mir_shard_spec.spl` (identity round-trip; unexecuted).
Unverified: a sharded Stage 2 native-build must show the package index published.

## Related: mir_phase_rss_retention_2026_10_24 workaround made permanent
- `mono_report_modules_owner_release()` became `mono_report_modules_take()`: the global is a
  one-shot transport (take + clear in one step), no workaround tag needed.
- The flat HIR store reset after MIR lowering stays as the permanent scoping point (its only
  readers are MIR lowering); comment rewritten, tag removed. Unexecuted.
