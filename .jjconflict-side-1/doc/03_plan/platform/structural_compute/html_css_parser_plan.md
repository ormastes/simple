# HTML/CSS Parser Plan (HTML-DOM + CSS-STYLE parse side)

**Date:** 2026-07-31 · **Status:** Proposed
**Parents:** architecture doc Part V (§13–§16); WebScene plan W3/W4
(`doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md`).

## Scope

Canonical SoA web data model and its parsers:

- `DomArena`/`DomAttributeArena`, stable document-local `NodeId`
  (index + generation), immutable DOM snapshots;
- HTML: GPU/SIMD tokenizer + **ordered** tree-builder commit (insertion modes,
  open-element stack, foster parenting, script interaction stay CPU-ordered);
  static-template profile for trusted no-script content, oracle-verified;
- CSS: tokenizer → component values → selector compilation to QueryIR →
  declaration/value bytecode → invalidation-feature extraction → indexes;
- DOM/CSS mutation transactions (`DomMutationBatch`, `CssChangeKind`) and the
  exact-invalidation strategy (§15.3), with `StyleDifference` classification.

Out of scope: layout (layout lanes), cascade GPU execution beyond parity
fixtures (webrender lane W4 execution tiers), media decoding.

## Owned paths

```text
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/ingest/
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/dom/
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/style/     # parse/index side
test/01_unit/lib/gpu_web/ingest/
test/01_unit/lib/gpu_web/style/
```

(Same paths as WebScene W3/W4 — this plan is their structural-compute
elaboration; ownership ledger `doc/03_plan/agent_tasks/gpu_web_scene/ownership.sdn`
remains the arbiter.)

## Dependencies

- parser_framework lane (HTML/CSS are ParseDialects on its runtime);
- frozen QueryIR (selector programs), MutationIR (DOM/CSSOM transactions),
  DirtyMask/invalidation contracts;
- gpu_mmu for resident arenas only.

## Phases

1. **Canonical schema (Wave 0/1).** DOM/CSS arenas + CPU parsers behind the
   current browser interfaces; WPT-derived comparison corpus.
2. **Selector QueryIR + invalidation features (Wave 6).** Feature indexes
   (rightmost key, ancestor keys, sibling/structural/`:has`/custom-property
   sensitivity); computed-style sharing + fingerprints.
3. **Mutation transactions (Wave 6).** Bounded command buffers, event-epoch
   commit, exact candidate invalidation; full-recompute oracle comparison.
4. **SIMD/GPU tokenizers (Wave 4).** HTML state summaries + prefix-state
   composition; CSS token/selector batches; capacity-checked count/scan/emit.

## Acceptance

- Token and DOM canonical serialization equal CPU oracle; deterministic
  malformed-input errors.
- Every incremental style result equals full recomputation for the same
  snapshot; paint-only changes never force layout.
- Selector conformance fixtures pass; specificity/origin/layer/importance
  ordering matches the CSS domain resolver.
- All writes capacity-checked; no pointer/array relocation; untrusted-input
  quotas enforced.
