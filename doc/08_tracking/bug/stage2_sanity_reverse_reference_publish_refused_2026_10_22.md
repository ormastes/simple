# Stage 2 sanity: `transient HIR scope end failed` on p2_add (reverse-reference publish chain)

Date: 2026-10-22
Status: open — failing node identified via instrumentation (landed); candidate rebuild pending

## Observed failure

Lane A: `bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
--mode=dynload --jobs=half` on release/1.0 @ c53a65fe (aarch64-apple-darwin).
The freshly built stage-2 candidate failed the sanity gate compiling
`src/compiler/bootstrap_admission/p2_add.spl`:

```
[ERROR]   transient HIR scope end failed for .../p2_add.spl
candidate_frontend_smoke: p2_add-build failed (raw rc=1)
VERDICT — ABORTED: stage=stage2
```

Full log: `/Users/ormastes/p3-lane/bootstrap-stage2.log`.

## Red herring eliminated

`[frontend-cache] store failed: cannot write under
.../stage2-tmp/simpleos-host-gpu-admission.*/cache/default/frontend` appears
just before the failure but is non-fatal by design
(`frontend_parse_cache.spl`: "a cache that cannot store is a slow build, not
a wrong one"). It forces a reparse; the failure is downstream.

## Failure locus

`driver_hir_pipeline_lowering.spl:581-583` (retained HIR lowering):
`driver_publish_reverse_reference_parse_scope_v1(token)` returned false.
That helper (`driver_hir_pipeline_support.spl`) is an AND-chain over three
nodes:

1. `reverse_reference_module_seal_v1` — batch seal + `transient_promote` of
   the Option carrier; returns `owned` (false when the promote refuses).
2. `driver_end_transient_parse_scope`
3. `reverse_reference_module_publish_v1` — refuses unless
   `batch.sealed and batch.valid` survived to publication.

The 2026-10-20 seed fix (store-back after `unwrap()` mutation,
`reverse_reference_batch_writeback_spec.spl`) is present in-tree; the same
class of defect re-appears in the SELF-HOSTED candidate by a different
mechanism (candidate codegen/runtime classification, same family as
`stage2_sanity_module_path_naming_probe_segv_2026_10_22.md` and the
`rt_transient_heap_promote` empty-immortal-array fix recorded in
`stage2_sanity_transient_parser_ownership_panic_2026_10_22.md`).

Suspect: node 1 — `transient_promote(batch)` on a batch whose array limbs
(`facts`, `known_families`, ...) are EMPTY for a tiny source like p2_add, so
the root classifies as not-transient-owned and the promote refuses. p2_add
has no reverse-reference facts by construction.

## Instrumentation landed

`driver_publish_reverse_reference_parse_scope_v1` now eprints
`[rr-publish] node=<seal|end|publish> ok=false token=...` naming the exact
refusing node. Rebuild the stage-2 candidate and read the sanity log.

## Notes

- The unrelated `hir-flatpool` MIR work tracked in updates 10/11
  (`mir_worker_flatpool_*` bug docs) concerns a different lane.
- The stage-2 cache required `--invalidate-cache=stage2` after the source
  identity moved (expected; old cache preserved by the script).
