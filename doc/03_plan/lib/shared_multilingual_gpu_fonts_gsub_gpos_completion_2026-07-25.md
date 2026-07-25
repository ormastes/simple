<!-- codex-design -->
# Pinned-Corpus GSUB/GPOS Completion Plan

Status: planned; implementation remains NO-GO after the third GPOS review.

Selected scope: shared multilingual GPU fonts Option A + NFR A. Complete every
active layout operation reached by the pinned Latin, Han, Devanagari,
Arabic/Urdu, and Cyrillic witnesses. Execute the deduplicated feature lookup
union in ascending OpenType LookupList order. Validate the whole active plan
before mutation and fail closed on unsupported behavior.

## Frozen boundaries

- Selector APIs: `select_gsub_lookup_plan`, `select_gpos_lookup_plan`.
- Internal record: `LayoutGlyphRecord`, including logical source, cluster,
  advances, offsets, and ligature `component_clusters`.
- Application APIs:
  `layout_validate_gsub_with_catalog`,
  `layout_apply_gsub_with_catalog`,
  `gpos_validate(font, active, catalog, records)`, and
  `gpos_apply(font, active, catalog, records)`.
- Public output remains `ShapedGlyph -> ShapedRun -> FontGlyphRun ->
  DrawIrGlyphRunPayload`.
- No lookup, face, atlas, cache, or backend resource enters Draw IR.
- `FontRenderer` and transient `FontRenderBatch` remain the only material owner.

## Accepted foundation

The selector slice has highest-capability static-review GO:

- correct `GSUB`/`GPOS` tags and layout versions;
- exact Script/LangSys, Script default, then absent-script `DFLT`;
- standards-ordered lookup union;
- valid-empty distinct from malformed;
- nearest-sibling section bounds;
- bounded FeatureVariations handling;
- retained MarkFilteringSet; and
- focused malformed/alias/index/order fixtures.

The GSUB slice has highest-capability static-review GO for the selected
operation union: types 1/2/4/5/6, required formats, nested catalog dispatch,
GDEF ignore-mark/mark-filter behavior, bounded recursion/work, atomic rollback,
and ligature component provenance.

Neither slice has executable acceptance until a current pure-Simple self-host
runs its focused specs.

## Remaining GPOS blockers

These are release blockers, not optional cleanup:

1. **Pair filtering:** LookupFlags always filter glyph 2. `valueFormat2`
   controls scan advancement only; it never bypasses filtering.
2. **Scan advancement:** PairPos with nonempty ValueRecord2 advances beyond
   glyph 2; empty ValueRecord2 leaves glyph 2 eligible next. ChainContextPos
   advances beyond the matched input sequence, not its lookahead.
3. **Ligature association:** MarkToLigature chooses the logical component
   boundary from `component_clusters`; an intervening ignored mark belongs to
   the preceding component rather than requiring exact cluster equality.
4. **Total work bound:** Coverage, ClassDef, PairSet, anchor, mark-array, and
   chained-context loops debit one shared run/table-derived budget. A local
   per-array cap is not sufficient.
5. **Legal ClassDef sharing:** PairPos format 2 permits ClassDef1 and ClassDef2
   to reference the same ClassDef. Alias rejection preserves this exception.
6. **Production integration:** the shaper must build nominal records, validate
   both complete plans, apply GSUB then recompute advances then apply GPOS,
   scale once, preserve RTL/logical clusters, and derive completion flags from
   the generic results. Empty-only GPOS compatibility stubs must not remain the
   production route.

## Fresh-session implementation stages

### Stage 1 — GPOS semantic repair

Owner: one implementation agent. Reviewer: independent highest-capability
agent.

- Introduce an internal result carrying `valid`, `matched/applied`, and
  `next_index`.
- Apply only the first applicable subtable.
- Correct PairPos and ChainContextPos advancement.
- Replace exact-equality ligature component lookup with boundary selection:
  choose the greatest component cluster not after the mark in logical order,
  with RTL handled by logical clusters rather than visual array order.
- Thread one mutable work budget through every variable-count reader.
- Permit one shared PairPos2 ClassDef while rejecting unrelated overlap.
- Keep all late failures transactional.

Required focused tests:

- filtered second glyph with ValueRecord2 empty and nonempty;
- PairPos advancement in both cases;
- ChainContextPos matched-input advancement;
- ignored mark between ligature components;
- shared ClassDef legal case plus illegal overlap;
- table-sized Coverage/ClassDef/PairSet work exhaustion; and
- malformed late lookup returning the original record vector.

Stop after at most three repair/review cycles. A third NO-GO is reported rather
than retried.

### Stage 2 — Canonical shaper integration

Owner: highest-capability implementation agent because this changes completion
truth.

1. Map selected runs to fixed OpenType tags:
   `latn`, `hani`, `dev2`, `arab`, and `cyrl`, with the selected four-byte
   language tags.
2. Keep Latin/Han/Cyrillic valid-empty under the explicit-feature policy.
3. Use the pinned default feature sets for Hindi and Arabic/Urdu plus explicit
   user features.
4. Build nominal glyph records from cmap and hmtx.
5. Validate GSUB and GPOS, including reachable catalog lookups, before mutation.
6. Apply GSUB, recompute advances for substituted glyph IDs, then apply GPOS.
7. Scale font-unit advances/offsets once and convert positive-up OpenType Y to
   positive-down Draw IR Y once.
8. Reverse visual RTL output only after logical shaping; preserve logical
   clusters and component provenance.
9. Set substitution and positioning completion independently. An incomplete
   phase makes `FontGlyphRun.valid=false` and retains
   `font-shaping-unavailable`.
10. Keep pinned Arabic/Devanagari implementations as regression oracles until
    generic parity passes; they no longer independently promote completion.

### Stage 3 — Incremental verification

Use only an admitted current pure-Simple self-host. Never use the Rust seed.
Run each criterion once:

1. parser selector spec;
2. generic GSUB spec;
3. generic GPOS spec;
4. pinned Devanagari and Arabic specs;
5. shaper unit spec;
6. shared shaping system spec;
7. Draw IR SDN round-trip and Engine2D shaped-material checks; and
8. `check src/lib`.

The runner must first pass the existing failing/empty calibration fixtures.
Any signal exit, unresolved symbol, zero executed examples, or absent summary
is a blocker rather than a pass.

### Stage 4 — Evidence and documentation

- Regenerate the mirrored shared-shaping manual with zero stubs.
- Retain the frozen step
  `step("Shape selected Unicode scripts with the pinned face")`.
- Show a nonzero bearing or GPOS offset through the handle-free Draw IR
  round-trip and canonical Engine2D `FontRenderer`.
- Update the bug record only after executable corpus and renderer evidence pass.
- Keep the claim explicitly pinned-corpus complete, not specification-wide
  GSUB/GPOS.

## Merge and push gates

- No file exceeds 800 lines.
- `git diff --check` passes.
- `find doc/06_spec -name '*_spec.spl' | wc -l` is `0`.
- Direct environment/runtime guards pass for working and staged changes.
- Independent highest-capability review reports GO.
- Runtime checks above pass once each.
- Commit only owned files; preserve unrelated worktree changes.
- Fetch and rebase onto current `origin/main`; abort if tracked file count
  decreases; then push the isolated branch.
