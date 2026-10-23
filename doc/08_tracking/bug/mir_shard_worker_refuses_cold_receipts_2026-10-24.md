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

## Workaround (`workaround(mir-shard-cold-receipts)`)
Shard worker/link child (SIMPLE_MIR_SHARD_QUEUE / SIMPLE_MIR_SHARD_LINK set) skip the receipts
requirement and drop `ctx.cold_hir_typed_receipts` after the eligibility check, so cold object
persistence is a no-op there. `capture_cold_hir_typed_receipts_v1` is unchanged. Trade-off:
cold HIR object persistence is not performed for sharded builds. Unverified until a Stage 2
built from this tree runs a sharded native-build.
