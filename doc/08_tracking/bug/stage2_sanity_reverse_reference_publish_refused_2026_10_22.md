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

## Field-level verdict (2026-10-23, lane A rerun 3)

```
[rr-publish] publish refused token=1 batch_token=-525297044564342979
  batch_gen=15726932 owner_gen=1 active=true sealed=false valid=false
```

The publish node refuses because EVERY scalar limb of the promoted batch
class reads back garbage across the transient-scope end: `batch_token` and
`batch_generation` are corrupted i64s and `sealed`/`valid` read false even
though seal set and stored them back. Module globals read correctly in the
same process (`active=true owner_gen=1`). The array (handle) limbs are
unaffected — the same mixed scalar+array inline-class corruption family as
`stage2_sanity_module_path_naming_probe_segv_2026_10_22` (ParserModule
flatten), here transported through `transient_promote`.

Note: a rerun under heavy multi-agent load failed differently (frontend
smoke rc=124 timeout in parse of the single p2_add file) — that mode is
contention, not this defect.

## Workaround landed

`reverse_reference_facts.spl` mirrors the batch scalars in module globals
(`_rr_module_batch_{token,generation,sealed,valid}_g_v1`), which survive the
corruption; seal/publish/accepts_registration now validate against the
globals. The class and its array flows are unchanged. Proper repair remains
the runtime class-layout/copy fix for mixed scalar+array classes.

## Update 2026-10-23: workaround validated at the publish node; next site is the flat-pool bug

With the scalar-globals workaround landed (ab07dfa3), the sanity lane no
longer records `[rr-publish] publish refused` — the publish node now passes.
The candidate proceeds to a SIGABRT in
`compiler__frontend__core__flat_pool_codec__flat_pool_builder_push`
(rt_panic), which is the independently-tracked delegated-frontend
flat-pool bug (`stage2_mir_shard_flat_pool_text_len_minus1_2026-10-22.md`,
annotation 2026-10-23). The stage-2 gate therefore stays red on that bug;
further whack-a-mole on this lane stops here (cycle cap) — the runtime
class-layout fix and the flat-pool lifetime fix are the cures.

## Sibling line release/1.0.0 (ported from d819cb542b9)

The release/1.0.0 line hit the same refusal at a different probe and ported
this lane's scalar-global mirror as d819cb542b9. Its observations, merged here:

- Failing probe there: `hello_world_positional` in the SIMPLE_BOOTSTRAP=1
  frontend pass (`transient HIR scope end failed for
  src/compiler/bootstrap_admission/hello_world.spl`, raw rc=1), on merged
  963358b7f31 post PR #4172; attempt 20261023T005842, sanity checks_run=5.
- The bootstrap=0 pass ran all four probes clean (p2_add,
  stage2_mir_retention, stage2_module_path_naming, hello_world_positional).
- A manual fresh-cache replay of the identical argv/bootstrap/backend shape
  PASSED — heap-layout-sensitive, consistent with the by-value/aggregate
  transport corruption family, not a deterministic gate disagreement.
- d819cb542b9's code is a subset of what this line already carries
  (ab07dfa3567 scalar mirror + ff1f69fd931 array-limb mirror), so only this
  evidence section was ported.
