<!-- codex-design -->
# Pinned-Corpus GSUB/GPOS Completion Plan

Status: reviewed plan; implementation remains NO-GO after the third GPOS
review. Three independent plan reviews on 2026-07-25 found the missing
traceability and executable gates corrected below; they did not accept the
implementation drafts.

Selected scope: shared multilingual GPU fonts Option A + NFR A. Complete every
active layout operation reached by the pinned Latin, Han, Devanagari,
Arabic/Urdu, and Cyrillic witnesses. Execute the deduplicated feature lookup
union in ascending OpenType LookupList order. Validate the whole active plan
before mutation and fail closed on unsupported behavior.

## Frozen boundaries

- Selector APIs: `select_gsub_lookup_plan`, `select_gpos_lookup_plan`.
- Internal records: `LayoutGlyphRecord`, including logical source, cluster,
  advances, offsets, ligature `component_clusters`, and a bounded feature mask;
  and `LayoutLookupActivation`, retaining lookup index plus the feature mask
  that activated it.
- Application APIs:
  `layout_validate_gsub_with_catalog`,
  `layout_apply_gsub_with_catalog`,
  `gpos_validate(font, active, catalog, records)`, and
  `gpos_apply(font, active, catalog, records)`.
- Public output remains `ShapedGlyph -> ShapedRun -> FontGlyphRun ->
  DrawIrGlyphRunPayload`.
- No lookup, face, atlas, cache, or backend resource enters Draw IR.
- `FontRenderer` and transient `FontRenderBatch` remain the only material owner.

## Frozen corpus and feature policy

The authoritative operation inventory is
`doc/01_research/local/shared_multilingual_gpu_fonts.md`, section
“Selected Option A active-plan inventory”. It freezes the operation union, but
not yet the per-face LookupList indices. Stage 0 below must freeze those exact
indices before implementation begins:

| Witness | Script/LangSys | Active default policy | Required operation union |
|---|---|---|---|
| English | `latn`/default | required features only; no optional defaults | valid-empty GSUB/GPOS |
| Simplified Chinese | `hani`/default | required features only; no optional defaults | valid-empty GSUB/GPOS, including the inactive v1.1 FeatureVariations table |
| Russian | `cyrl`/default | required features only; no optional defaults | valid-empty GSUB/GPOS |
| Hindi `हिन्दी` | `dev2`/`HIN ` (resolved default) | the pinned Indic GSUB list and GPOS `abvm blwm dist kern` | GSUB 2/4/5/6 and GPOS 2/4/6/8/9 |
| Arabic witness | `arab`/default | pinned Arabic defaults | GSUB 1/2/4/5/6 and GPOS 2/4/5/6/8 |
| Urdu witness | `arab`/`URD ` | pinned Urdu defaults | GSUB 1/2/4/5/6 and GPOS 2/4/5/6/8 |

The exact selected formats are GSUB 1.1/1.2, 2.1, 4.1, 5.1/5.2/5.3, and
6.1/6.2/6.3; GPOS 2.1/2.2, 4.1/5.1/6.1, 8.3, and ExtensionPos 9.1 wrapping
PairPos 2.1/2.2. Active LookupFlags are `0`, `0x0008`, and `0x0010`.
ExtensionPos remains a top-level inventory entry and must be validated and
applied fail-closed. Any regenerated pinned plan containing another unlisted
operation remains incomplete until the inventory and selected scope are
reviewed.

Required LangSys features are always active. The script defaults above are
additive. `Shaper.features_enabled` adds only its existing boolean optional
feature tags; disable requests and alternate numeric feature values are outside
this API and cannot be silently approximated. Selection must retain enough
feature-to-lookup provenance for script preprocessing to restrict positional
features to eligible glyphs even after the final lookup union is deduplicated
and sorted.

For RTL `arab` selection, required LangSys features remain additive. Request
GSUB tags `rtlm ccmp locl isol fina fin2 fin3 medi med2 init rlig calt rclt
liga clig mset stch` and GPOS tags `curs kern mark mkmk`. Activate a requested
tag only when advertised by the resolved LangSys; an absent tag is a no-op.
Deduplicate and execute the resulting union in ascending LookupList order. This
is the pinned Simple policy derived from HarfBuzz commit
`d65aa90ea656aa1e31ff26b7d052ef2eaa1f418a`, not full HarfBuzz pause/stage
parity.

### Runtime prerequisite for every executable stage

Use only a current pure-Simple self-host; never use the Rust seed. Before Stage
0, set `SIMPLE_BIN` to `bin/release/<host-triple>/simple`,
`release/<host-triple>/simple`, or
`build/bootstrap/full/<host-triple>/simple`, then admit and record it once:

```sh
CANDIDATE_FRONTEND_ROOT=$PWD
. scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs
simple_binary_is_valid "$SIMPLE_BIN"
mkdir -p build/test-artifacts/shared_multilingual_gpu_fonts
sha256sum "$SIMPLE_BIN" \
  >build/test-artifacts/shared_multilingual_gpu_fonts/admitted-simple.sha256
```

Any failed admission blocks every executable stage; it does not authorize
another runtime.

### Stage 0 — Per-face inventory freeze

Owner: one read-only inventory agent followed by one test/fixture implementation
agent. Owned paths are the SDN fixture and its focused spec below. The handoff
is the exact per-face rows plus pinned asset hashes; an independent
highest-capability reviewer validates them against the font bytes. `/root` is
merge owner.

Before changing the application engine, add
`test/fixtures/fonts/shared_multilingual_gpu_fonts/active_layout_plan_inventory.sdn`.
It has one row per pinned face/script/LangSys/feature and records the asset
SHA-256, table, feature tag, ascending LookupList index, lookup type, every
active subtable format, LookupFlags, and MarkFilteringSet. It covers Noto Sans
SC, Noto Serif SC, Noto Sans/Serif Devanagari, and Noto Sans/Naskh Arabic for
the witness rows above. Latin, Han, and Cyrillic each have explicit GSUB and
GPOS valid-empty rows with `selected_lookup_count: 0`; absence is not
equivalent to empty. The existing Arabic compatibility arrays are discovery
inputs, not acceptance truth.

Add `test/01_unit/lib/skia/ot_layout_pinned_inventory_spec.spl`. It loads each
registry-pinned blob, independently selects the required/default/explicit
features, compares every ordered field to the SDN row, and asserts both that
all fixture rows, including all twelve valid-empty table rows—six per SC
face—were consumed and that no selected lookup was omitted.
The Stage 0 oracle reads the pinned Layout tables directly and must compile
against committed `HEAD`; it does not depend on uncommitted production-selector
fields. Production selector parity remains a Stage 2 gate against this frozen
oracle. Run:

```sh
SIMPLE_LIB=src SIMPLE_NO_STUB_FALLBACK=1 "$SIMPLE_BIN" test \
  test/01_unit/lib/skia/ot_layout_pinned_inventory_spec.spl \
  --mode=interpreter --no-session-daemon --sequential --no-db --no-cache \
  --assert-ran --fail-fast
```

The fixture and spec require independent highest-capability review. Any asset
hash or selected-plan drift is a fail-closed scope change, not an automatic
fixture refresh.

## Requirement traceability

| Contract | Owning source seam | Executable evidence | Pass condition |
|---|---|---|---|
| REQ-007 selected-corpus shaping | `ot_parser_layout.spl`, `ot_layout_apply.spl`, `ot_layout_gpos.spl`, `shaper.spl` | parser/apply/GPOS/shaper unit specs and `shared_font_shaping_acceptance_spec.spl` | exact pinned glyph, cluster, advance, offset, direction, and face identity; both completion flags true |
| Option A active-plan completeness | selector plus pinned per-face SDN inventory | pinned-inventory, parser, and shared-shaping specs | exact ordered lookup/type/format/flag inventory; zero unsupported active entries |
| NFR A fail-closed atomicity | selector, GSUB, and GPOS validators | malformed/late-failure unit fixtures | valid-empty differs from malformed; original records survive every validation/apply failure |
| NFR A total work bound | one run/table-derived budget threaded through layout readers | GSUB/GPOS exhaustion fixtures | deterministic incomplete result before over-budget traversal; no partial mutation |
| Canonical material boundary | `_resolve_selected_shaped_glyph_run`, Draw IR SDN, Engine2D `FontRenderer` | SDN, renderer, and shared-surface specs | handle-free round-trip and nonzero positioned material through the selected face |
| Existing cache/perf contract | resolved-metrics cache and existing font perf evidence owner | `shared_multilingual_gpu_fonts_perf_spec.spl` and its durable `evidence.env` | no new shaping cache; collector exits 0 and its own `expect_font_perf_budget` assertion accepts the refreshed record |

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
agent. Owned paths are `src/lib/skia/feature/shaper/ot_layout_gpos.spl`,
`ot_layout_context.spl`, and their two focused unit specs. The handoff is a
reviewed diff plus one result line per required focused test; `/root` is merge
owner.

- Introduce an internal result carrying `valid`, `matched/applied`, and
  `next_index`.
- Apply only the first applicable subtable.
- Correct PairPos and ChainContextPos advancement.
- Replace exact-equality ligature component lookup with boundary selection:
  choose the greatest component cluster not after the mark in logical order,
  with RTL handled by logical clusters rather than visual array order.
- Thread one mutable work budget through every variable-count reader.
- Permit one shared PairPos2 ClassDef while rejecting unrelated overlap.
- Implement GPOS ExtensionPos format 1 as a validated wrapper over the shared
  semantic GPOS handlers, preserving the outer LookupFlag and shared work
  budget. Reject recursive type 9, invalid extension offsets, unsupported
  wrapped types/formats, and cross-table reads before mutation.
- Keep all late failures transactional.

Required focused tests:

- filtered second glyph with ValueRecord2 empty and nonempty;
- PairPos advancement in both cases;
- ChainContextPos matched-input advancement;
- ignored mark between ligature components;
- shared ClassDef legal case plus illegal overlap;
- table-sized Coverage/ClassDef/PairSet work exhaustion;
- exact validation of Noto Serif Devanagari lookup 36's three ExtensionPos
  wrappers plus malformed, recursive, unsupported, and out-of-range targets;
  and
- malformed late lookup returning the original record vector.

Stop after at most three repair/review cycles. A third NO-GO is reported rather
than retried.

### Stage 2 — Canonical shaper integration

Owner: highest-capability implementation agent because this changes completion
truth. After the Stage 1 handoff, this agent owns
`src/lib/skia/feature/glyph/ot_parser_layout.spl`,
`src/lib/skia/feature/shaper/shaper.spl`, `ot_layout_context.spl`,
`ot_layout_apply.spl`, `ot_layout_gpos.spl`, their focused specs, and the
shared shaping scenario. Stage 1 makes no further edits after handoff. The
independent final reviewer owns the GO/NO-GO verdict; `/root` merges.

1. Map selected runs to the exact script/LangSys/default-feature rows in the
   frozen corpus table above.
2. Keep Latin/Han/Cyrillic valid-empty under the explicit-feature policy.
3. Use the pinned default feature sets for Hindi and Arabic/Urdu plus explicit
   user features. Assign one stable bit per active feature within the bounded
   selected plan.
4. Implement bounded ContextSubst format 1 rule-set validation/application
   through the existing nested dispatcher. Cover match, miss, malformed
   rule-set, malformed nested dispatch, and shared-budget exhaustion before
   integration.
5. Extract the joining/reordering decisions from the existing pinned Arabic and
   Devanagari shapers into logical preprocessing functions. They return nominal
   `LayoutGlyphRecord` values and feature masks; they no longer substitute,
   position, reverse, or promote completion. Unsupported text outside the exact
   witnesses remains incomplete.
6. Arabic preprocessing assigns `isol`/`init`/`medi`/`fina` eligibility in
   logical order. Indic preprocessing assigns the pinned syllable-stage
   eligibility and reorder while preserving source/cluster provenance.
   Run-wide required and explicit optional features set their bits on every
   eligible record.
7. Expand `LayoutLookupPlan` from bare indices to ordered
   `LayoutLookupActivation` values. Each activation contains the union of
   feature bits that selected the lookup; applying a lookup requires an
   intersection with the current record's mask. Single/multiple replacements
   inherit the source mask; a ligature keeps the intersection of consumed
   component masks.
8. Contextual substitution/positioning passes the invoking activation mask into
   nested catalog dispatch. The nested lookup applies only at the matched target
   and only when that target record intersects the inherited mask; it cannot
   regain a feature bit removed by preprocessing or a prior substitution.
9. Build nominal font-unit advances from hmtx and retain the preprocessing
   eligibility on records and lookup activations.
10. Validate GSUB and GPOS, including reachable catalog lookups, before mutation.
11. Apply GSUB, recompute font-unit advances for substituted glyph IDs, then
   apply GPOS.
12. Convert font units to `ShapedGlyph` values once after GPOS and before
   `ShapedRun` position construction. Use the existing deterministic integer
   rounding and convert positive-up OpenType Y to positive-down Draw IR Y once.
13. Reverse visual RTL output only after logical shaping; preserve logical
   clusters and component provenance.
14. Set substitution and positioning completion independently. An incomplete
   phase makes `FontGlyphRun.valid=false` and retains
   `font-shaping-unavailable`.
15. Integrate through `_resolve_selected_shaped_glyph_run`; retain its live face
    identity check and keep Draw IR handle-free.
16. Keep pinned Arabic/Devanagari implementations as regression oracles until
    generic parity passes; they no longer independently promote completion.

Required Stage 2 tests add:

- explicit valid-empty Latin, Han, and Cyrillic inventory rows;
- Arabic and Indic positional-feature masks on logical records;
- nested contextual lookup applying only at a mask-eligible matched target;
- replacement/ligature mask propagation; and
- exact generic parity with both pinned compatibility oracles.

### Stage 3 — Incremental verification

Reuse the runtime admitted before Stage 0. Before focused results, configure
and calibrate the same isolated runner once:

```sh
export SIMPLE_LIB=src
export SIMPLE_NO_STUB_FALLBACK=1
TEST_FLAGS="--mode=interpreter --no-session-daemon --sequential --no-db --no-cache --assert-ran --fail-fast"
mkdir -p build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration
set +e
"$SIMPLE_BIN" test scripts/check/fixtures/font_evidence_runner_fail_spec.spl \
  $TEST_FLAGS \
  >build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/fail.log 2>&1
fail_status=$?
set -e
test "$fail_status" -eq 1
grep -Fq 'Results: 1 total, 0 passed, 1 failed' \
  build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/fail.log
grep -Fq 'FAIL' \
  build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/fail.log
set +e
"$SIMPLE_BIN" test scripts/check/fixtures/font_evidence_runner_empty_spec.spl \
  $TEST_FLAGS \
  >build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/empty.log 2>&1
empty_status=$?
set -e
test "$empty_status" -eq 1
grep -Fq -- '--assert-ran: no BDD examples executed' \
  build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/empty.log
! grep -Fq 'test-runner: native result wrapper complete' \
  build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/empty.log
```

Exit 2/124/132/139, a missing exact message, or a completion marker in the empty
fixture blocks all focused claims.

Then run each command once with the same exported environment and `$TEST_FLAGS`;
require exit 0, a nonzero executed-example count, and the normal
passed/failed/skipped summary:

```sh
"$SIMPLE_BIN" test test/01_unit/lib/skia/ot_parser_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" test test/01_unit/lib/skia/ot_layout_pinned_inventory_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" test test/01_unit/lib/skia/ot_layout_apply_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" test test/01_unit/lib/skia/ot_layout_gpos_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" test test/01_unit/lib/skia/selected_devanagari_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" test test/01_unit/lib/skia/selected_arabic_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" test test/01_unit/lib/skia/shaper_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" test test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" test test/01_unit/lib/common/ui/draw_ir_sdn_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" test test/01_unit/lib/common/text_layout/font_renderer_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" test test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl $TEST_FLAGS
"$SIMPLE_BIN" check src/lib
"$SIMPLE_BIN" test test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl $TEST_FLAGS
```

The performance command is a promoted-host gate, not an availability pass. It
must exit 0, write
`build/shared_multilingual_gpu_fonts_perf/evidence.env`, and pass the spec's
`durable.status == "pass"` and `expect_font_perf_budget(durable)` assertions.
An unavailable Vulkan/device row keeps the overall font release pending.

The runner must first pass the existing failing/empty calibration fixtures.
Any signal exit, unresolved symbol, zero executed examples, or absent summary
is a blocker rather than a pass.

### Stage 4 — Evidence and documentation

- Regenerate and check the mirrored shared-shaping manual:

  ```sh
  docgen_log=build/test-artifacts/shared_multilingual_gpu_fonts/shaping-docgen.log
  mkdir -p "$(dirname "$docgen_log")"
  "$SIMPLE_BIN" spipe-docgen \
    test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl \
    --output doc/06_spec --no-index >"$docgen_log" 2>&1
  grep -Fq '0 stubs' "$docgen_log"
  ```

  Both the command and grep must exit 0.
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
- `sh scripts/audit/direct-env-runtime-guard.shs --working` and
  `sh scripts/audit/direct-env-runtime-guard.shs --staged` both pass.
- Independent highest-capability review reports GO.
- Runtime checks above pass once each.
- The verify report maps every row in the traceability table to current evidence
  and ends with `STATUS: PASS`.
- After all commands above, an independent highest-capability reviewer runs the
  six-phase workflow in `.codex/skills/verify/SKILL.md`, writes its terminal
  report to
  `build/test-artifacts/shared_multilingual_gpu_fonts/gsub-gpos-verify.log`, and
  the merge owner runs
  `grep -qx 'STATUS: PASS' build/test-artifacts/shared_multilingual_gpu_fonts/gsub-gpos-verify.log`.
- Commit only owned files; preserve unrelated worktree changes.
- Fetch and rebase onto current `origin/main`; abort if tracked file count
  decreases; then push the isolated branch.
