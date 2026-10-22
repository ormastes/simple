# Stage-2 sanity: reverse-reference publish refused — scalar limbs of the promoted batch corrupt (2026-10-22/23)

**Status:** WORKED AROUND (scalar mirror in module globals, same as the
release/1.0 sibling lane ab07dfa3567); proper repair remains the runtime
class-layout/copy fix for mixed scalar+array inline classes.

## Symptom

Stage-2 sanity on release/1.0.0 (merged 963358b7f31, post PR #4172) fails the
bootstrap=1 frontend pass at the hello_world_positional probe:

```
[ERROR] phase 3 FAILED
[ERROR]   transient HIR scope end failed for src/compiler/bootstrap_admission/hello_world.spl
error: in-process native-build: transient HIR scope end failed for src/compiler/bootstrap_admission/hello_world.spl
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
```

The bootstrap=0 pass runs the identical four probes clean (p2_add,
stage2_mir_retention, stage2_module_path_naming, hello_world_positional all
raw_status=0); only the SIMPLE_BOOTSTRAP=1 pass refuses, and the failure is
not deterministic under a plain manual replay (a fresh-cache replay of the
same argv/bootstrap/backend shape passed) — heap-layout-sensitive, the
signature of the by-value/aggregate transport corruption family.

## Failure locus

`driver_hir_pipeline_lowering.spl:581` — `driver_publish_reverse_reference_parse_scope_v1`
returns false; the refusing node is `reverse_reference_module_publish_v1`
(`reverse_reference_facts.spl`), reached after `driver_end_transient_parse_scope`.

## Root cause (field-level verdict from the release/1.0 sibling lane)

The release/1.0 lane hit the byte-identical refusal (there on p2_add) and
instrumented every node. Field-level result, recorded in that lane's bug doc:

```
[rr-publish] publish refused token=1 batch_token=-525297044564342979
  batch_gen=15726932 owner_gen=1 active=true sealed=false valid=false
```

Every scalar limb (token/generation/sealed/valid) of the
transient_promote'd `ReverseReferenceModuleBatchV1` (a mixed scalar+array
inline class) reads back garbage across the scope end in the self-hosted
candidate, while module globals (`active=true owner_gen=1`) and the array
(handle) limbs read correctly. Seal itself succeeds because it validates
before the corrupting scope end; publish fails because it validates after.

Same family as `stage2_sanity_module_path_naming_probe_segv_2026_10_22`
(class-with-large-inline-struct field; fixed there by flattening to
handle-sized limbs) and the NLL `live_aliases` method-arg corruption (fixed
by free-function conversion). The proper repair here is likewise in the
runtime class-layout/copy for mixed scalar+array classes.

## Workaround landed

`reverse_reference_facts.spl` mirrors the batch scalars in module globals
(`_rr_module_batch_{token,generation,sealed,valid}_g_v1`), which survive the
corrupting transport; `seal` mirrors the seal, `publish` and
`accepts_registration` validate against the globals. The batch class and its
array flows are unchanged. A refusal now prints a field-level `[rr-publish]`
diagnostic instead of failing silently.

## Evidence

- 2026-10-23 release/1.0.0 lane (attempt 20261023T005842, pid 27345): sanity
  status=fail, checks_run=5; bootstrap-0 pass fully green;
  `stage2-sanity.env.frontend-failure.log` carries the exact text above.
- Manual replay of the identical probe shape (rejected candidate,
  SIMPLE_BOOTSTRAP=1, fresh cache) PASSED — consistent with layout-sensitive
  corruption, not a deterministic gate disagreement.
- release/1.0 sibling lane (commits c35d36f0d21 → fad1bd8c37f → ab07dfa3567,
  bug doc `stage2_sanity_reverse_reference_publish_refused_2026_10_22.md`
  there) proved the field-level cause and that the scalar-global mirror
  unblocks the stage-2 gate.
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
