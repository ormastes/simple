# Landed specs import modules absent from origin/main (2026-08-08)

Status: DUPLICATE of lib_specs_import_133_modules_that_do_not_exist_2026-08-04.md
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Summary

122 tracked `*_spec.spl` files on `origin/main` (68 unique basenames; the rest
are the known `test/unit` + `test/01_unit` tree duplication) contain a
`use std.<module>` whose module does not exist anywhere on `origin/main`.

These are invisible in the shared working copy — the WC has files that were
never landed, so the specs look fine locally and are broken for every clone.

## How this was found (and the oracle trap that hid it)

The originating report claimed `test/unit/lib/std_hash_facade_spec.spl` was
orphaned because `git cat-file -e origin/main:src/std/hash.spl` fails.

**That check is a guaranteed false positive.** `src/std` is a SYMLINK BLOB in
git (mode 120000 -> `lib`), so NO path under `src/std/` ever resolves via
`git cat-file` — `src/std/spec.spl`, `src/std/common.spl`, `src/std/core` all
"fail" identically. `src/lib/hash.spl` is on origin/main and exports every name
that spec imports. Measured on a pristine `git archive origin/main` tree:

    SPEC FILE VERDICT: test/unit/lib/std_hash_facade_spec.spl declared>=5 \
      executed=5 passed=5 failed=0 dropped=0

Any sweep of this class MUST map `std.*` -> `src/lib/*`, never `src/std/*`.

## Two subclasses

1. **Genuinely unlanded module** — e.g. `std.blink.layout.block_flow`;
   `src/lib/blink/` holds only 6 files, none under `layout/`. Likewise
   `src/lib/{test,system,sys,parser,ui,diagnostics,plugin,bare}` = 0 entries.
2. **Wrong `std.lib.` prefix** (28 imports) — e.g. `std.lib.skia.entity.geometry`
   while `src/lib/skia/` genuinely exists (104 files). There is no
   `src/lib/lib/`, so these are import-path typos, not missing code.

## Cluster breakdown (by missing top-level namespace)

    blink 66 | lib 28 | parser 18 | cc 16 | test 12 | bare 10 | sys 5
    system 4 | signature 2 | probability_utils 2 | plugin 2 | game_engine 2
    file 2 | ds_utils 2 | diagnostics 2 | collection_helpers 2
    ui 1 | prelude 1 | doctest 1 | app 1

## Oracle calibration (two-sided — required, see below)

The first version of the resolver **FAILED OPEN**: progressive truncation let a
bare tier directory (`src/lib/nogc_sync_mut`) match, so every nonexistent module
resolved True. Fixed by never truncating below `seg[:1]`.

Final calibration: 14/14 known-good imports resolve (`std.spec`, `std.hash`,
`std.common`, `std.nogc_sync_mut.src.hash`, `std.gc_async_mut.spec`, ...) AND
4/4 planted-nonexistent modules flagged. The facade spec itself is correctly
NOT flagged. Resolution must model: direct `src/lib/<p>`, the tier fallback
(`nogc_sync_mut`, `gc_async_mut`, ...), an interior `src/` segment, and
`.spl` / `mod.spl` / `__init__.spl` forms — `src/lib/spec` does not exist yet
`use std.spec` works everywhere.

## Scope limits (do not over-read the number)

- Only imports beginning `std.` are checked; non-`std` imports are unchecked.
- Existence-only: it does not verify the module exports the named symbols.
- Flags are per spec-path, so the duplicated test trees double-count.

## Why no pre-push guard was landed

A guard would fail immediately on origin/main against 122 pre-existing flags —
that is a broken build, not a gate. Land one only after this family is triaged
to zero (or with an explicit grandfather list).

## Flagged specs

- examples/10_tooling/mate_broker/test/dashboard_ui_spec.spl -> std.ui.
- test/01_unit/app/llm_caret/messaging/caret_command_spec.spl -> std.test.
- test/01_unit/app/tooling/ds_utils_spec.spl -> std.ds_utils.
- test/01_unit/app/tooling/probability_utils_spec.spl -> std.probability_utils.
- test/01_unit/compiler/diagnostic_formatter_contract_spec.spl -> std.diagnostics.formatters.
- test/01_unit/compiler/linker/linker_wrapper_smf_spec.spl -> std.system.
- test/01_unit/compiler/linker/object_emitter_spec.spl -> std.system.
- test/01_unit/compiler/parser/treesitter_lexer_real_spec.spl -> std.parser.treesitter
- test/01_unit/compiler/parser/treesitter_parser_real_spec.spl -> std.parser.treesitter
- test/01_unit/compiler/parser/treesitter_tokenkind_real_spec.spl -> std.parser.treesitter
- test/01_unit/compiler/parser/treesitter_tree_real_spec.spl -> std.parser.treesitter
- test/01_unit/hal/hal_traits_spec.spl -> std.bare.hal.gpio.,std.bare.hal.i2c.,std.bare.hal.spi.,std.bare.hal.timer.,std.bare.hal.uart.
- test/01_unit/lib/blink/block_flow_spec.spl -> std.blink.layout.block_flow.
- test/01_unit/lib/blink/computed_style_spec.spl -> std.blink.entity.computed_style.
- test/01_unit/lib/blink/document_spec.spl -> std.blink.dom.document.
- test/01_unit/lib/blink/flex_spec.spl -> std.blink.layout.flex.
- test/01_unit/lib/blink/form_paint_spec.spl -> std.blink.dom.form_state.,std.blink.layout.block_flow.,std.blink.paint.paint_tree_walker.
- test/01_unit/lib/blink/hit_test_spec.spl -> std.blink.input.event.,std.blink.input.hit_test.,std.blink.layout.block_flow.,std.lib.skia.entity.geometry.
- test/01_unit/lib/blink/html_tokenizer_spec.spl -> std.blink.html_parser.
- test/01_unit/lib/blink/html_tree_builder_spec.spl -> std.blink.html_parser.,std.blink.html_parser.tree_builder.
- test/01_unit/lib/blink/image_paint_spec.spl -> std.blink.layout.block_flow.,std.blink.paint.paint_tree_walker.
- test/01_unit/lib/blink/inline_flow_spec.spl -> std.blink.layout.
- test/01_unit/lib/blink/input_event_spec.spl -> std.blink.input.event.
- test/01_unit/lib/blink/navigation_controller_spec.spl -> std.blink.navigation.controller.,std.blink.url.url_parser.
- test/01_unit/lib/blink/navigation_fetch_spec.spl -> std.blink.navigation.controller.,std.blink.network.fetch.
- test/01_unit/lib/blink/paint_artifact_spec.spl -> std.blink.entity.paint_artifact.
- test/01_unit/lib/blink/paint_chunk_spec.spl -> std.blink.entity.paint_chunk.,std.lib.skia.entity.geometry.
- test/01_unit/lib/blink/paint_controller_spec.spl -> std.blink.entity.paint_artifact.,std.blink.feature.paint.paint_controller.
- test/01_unit/lib/blink/paint_tree_walker_spec.spl -> std.blink.entity.computed_style.,std.blink.layout.block_flow.,std.blink.paint.paint_tree_walker.,std.lib.skia.entity.color.
- test/01_unit/lib/blink/scroll_manager_spec.spl -> std.blink.scroll.manager.
- test/01_unit/lib/blink/style_cascade_spec.spl -> std.blink.entity.computed_style.,std.blink.style.cascade.,std.lib.skia.entity.color.
- test/01_unit/lib/blink/url/url_parser_spec.spl -> std.blink.url.url_parser.
- test/01_unit/lib/cc/layer_base_spec.spl -> std.lib.cc.entity.layer_base.
- test/01_unit/lib/cc/layer_tree_host_spec.spl -> std.cc.entity.layer.,std.cc.entity.layer_tree_host.
- test/01_unit/lib/cc/picture_layer_impl_spec.spl -> std.cc.entity.layer.,std.cc.feature.picture_layer_impl.,std.cc.feature.raster_source.
- test/01_unit/lib/cc/property_tree_spec.spl -> std.lib.cc.entity.property_tree.
- test/01_unit/lib/cc/tile_manager_spec.spl -> std.cc.entity.tile.,std.cc.feature.raster_buffer_provider.,std.cc.feature.tile_manager.
- test/01_unit/lib/cc/tile_spec.spl -> std.lib.cc.entity.tile.
- test/01_unit/lib/content/web_contents_spec.spl -> std.blink.entity.paint_artifact.
- test/01_unit/lib/crypto/crypto_reference_spec.spl -> std.signature.key_ops
- test/01_unit/lib/std/common/collection_helpers_spec.spl -> std.collection_helpers.
- test/01_unit/lib/std/compiler/loader/jit_instantiator_spec.spl -> std.test.spipe.
- test/01_unit/lib/std/file/file_io_spec.spl -> std.file.
- test/01_unit/lib/std/game_engine/effects_spec.spl -> std.game_engine.effects.
- test/01_unit/lib/std/parser/error_recovery_spec.spl -> std.parser.error_recovery.
- test/01_unit/lib/text/text_index_slice_spec.spl -> std.lib.common.text.adapters,std.lib.common.text.text,std.lib.common.text.text_view
- test/01_unit/lib/text/text_length_spec.spl -> std.lib.common.text.adapters,std.lib.common.text.text
- test/01_unit/lib/text/text_search_spec.spl -> std.lib.common.text.adapters,std.lib.common.text.text
- test/01_unit/std/module_import_spec.spl -> std.test.helpers
- test/01_unit/std/parser/treesitter_node_spec.spl -> std.parser.treesitter_node.
- test/02_integration/lib/security/live_kms_transport_spec.spl -> std.sys.env
- test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl -> std.
- test/03_system/feature/app/fault_detection_spec.spl -> std.sys.fault_detection.
- test/03_system/feature/features/parser/parser_deprecation_warnings_spec.spl -> std.parser.
- test/03_system/feature/features/treesitter/treesitter_parser_spec.spl -> std.parser.treesitter.
- test/03_system/feature/language/modules_spec.spl -> std.prelude.
- test/03_system/feature/plugin/runtime_api_plugin_spec.spl -> std.plugin.
- test/03_system/feature/usage/parser_error_recovery_spec.spl -> std.parser.
- test/03_system/feature/usage/sandboxing_spec.spl -> std.sys.process
- test/feature/plugin/runtime_api_plugin_spec.spl -> std.plugin.
- test/feature/usage/parser_error_recovery_spec.spl -> std.parser.
- test/feature/usage/sandboxing_spec.spl -> std.sys.process
- test/integration/lib/security/live_kms_transport_spec.spl -> std.sys.env
- test/integration/lib/std/doctest/discovery_spec.spl -> std.doctest.discovery.
- test/system/features/parser/parser_deprecation_warnings_spec.spl -> std.parser.
- test/system/features/treesitter/treesitter_parser_spec.spl -> std.parser.treesitter.
- test/unit/app/slang_pack/main_spec.spl -> std.app.slang_pack.main.
- test/unit/app/tooling/ds_utils_spec.spl -> std.ds_utils.
- test/unit/app/tooling/probability_utils_spec.spl -> std.probability_utils.
- test/unit/compiler/blocks/builder_api_basic_spec.spl -> std.test.
- test/unit/compiler/blocks/builder_default_parser_spec.spl -> std.test.
- test/unit/compiler/blocks/easy_api_basic_spec.spl -> std.test.
- test/unit/compiler/blocks/testing_framework_spec.spl -> std.test.
- test/unit/compiler/blocks/utils_basic_spec.spl -> std.test.
- test/unit/compiler/diagnostic_formatter_contract_spec.spl -> std.diagnostics.formatters.
- test/unit/compiler/linker/linker_wrapper_smf_spec.spl -> std.system.
- test/unit/compiler/linker/object_emitter_spec.spl -> std.system.
- test/unit/compiler/mono/monomorphize_integration_spec.spl -> std.test.
- test/unit/compiler/parser/match_empty_array_bug_spec.spl -> std.test.
- test/unit/compiler/parser/treesitter_lexer_real_spec.spl -> std.parser.treesitter
- test/unit/compiler/parser/treesitter_parser_real_spec.spl -> std.parser.treesitter
- test/unit/compiler/parser/treesitter_tokenkind_real_spec.spl -> std.parser.treesitter
- test/unit/compiler/parser/treesitter_tree_real_spec.spl -> std.parser.treesitter
- test/unit/hal/hal_traits_spec.spl -> std.bare.hal.gpio.,std.bare.hal.i2c.,std.bare.hal.spi.,std.bare.hal.timer.,std.bare.hal.uart.
- test/unit/lib/blink/block_flow_spec.spl -> std.blink.layout.block_flow.
- test/unit/lib/blink/computed_style_spec.spl -> std.blink.entity.computed_style.
- test/unit/lib/blink/document_spec.spl -> std.blink.dom.document.
- test/unit/lib/blink/flex_spec.spl -> std.blink.layout.flex.
- test/unit/lib/blink/form_paint_spec.spl -> std.blink.dom.form_state.,std.blink.layout.block_flow.,std.blink.paint.paint_tree_walker.
- test/unit/lib/blink/hit_test_spec.spl -> std.blink.input.event.,std.blink.input.hit_test.,std.blink.layout.block_flow.,std.lib.skia.entity.geometry.
- test/unit/lib/blink/html_tokenizer_spec.spl -> std.blink.html_parser.
- test/unit/lib/blink/html_tree_builder_spec.spl -> std.blink.html_parser.,std.blink.html_parser.tree_builder.
- test/unit/lib/blink/image_paint_spec.spl -> std.blink.layout.block_flow.,std.blink.paint.paint_tree_walker.
- test/unit/lib/blink/inline_flow_spec.spl -> std.blink.layout.
- test/unit/lib/blink/input_event_spec.spl -> std.blink.input.event.
- test/unit/lib/blink/navigation_controller_spec.spl -> std.blink.navigation.controller.,std.blink.url.url_parser.
- test/unit/lib/blink/navigation_fetch_spec.spl -> std.blink.navigation.controller.,std.blink.network.fetch.
- test/unit/lib/blink/paint_artifact_spec.spl -> std.blink.entity.paint_artifact.
- test/unit/lib/blink/paint_chunk_spec.spl -> std.blink.entity.paint_chunk.,std.lib.skia.entity.geometry.
- test/unit/lib/blink/paint_controller_spec.spl -> std.blink.entity.paint_artifact.,std.blink.feature.paint.paint_controller.
- test/unit/lib/blink/paint_tree_walker_spec.spl -> std.blink.entity.computed_style.,std.blink.layout.block_flow.,std.blink.paint.paint_tree_walker.,std.lib.skia.entity.color.
- test/unit/lib/blink/scroll_manager_spec.spl -> std.blink.scroll.manager.
- test/unit/lib/blink/style_cascade_spec.spl -> std.blink.entity.computed_style.,std.blink.style.cascade.,std.lib.skia.entity.color.
- test/unit/lib/blink/url/url_parser_spec.spl -> std.blink.url.url_parser.
- test/unit/lib/cc/layer_base_spec.spl -> std.lib.cc.entity.layer_base.
- test/unit/lib/cc/layer_tree_host_spec.spl -> std.cc.entity.layer.,std.cc.entity.layer_tree_host.
- test/unit/lib/cc/picture_layer_impl_spec.spl -> std.cc.entity.layer.,std.cc.feature.picture_layer_impl.,std.cc.feature.raster_source.
- test/unit/lib/cc/property_tree_spec.spl -> std.lib.cc.entity.property_tree.
- test/unit/lib/cc/tile_manager_spec.spl -> std.cc.entity.tile.,std.cc.feature.raster_buffer_provider.,std.cc.feature.tile_manager.
- test/unit/lib/cc/tile_spec.spl -> std.lib.cc.entity.tile.
- test/unit/lib/content/web_contents_spec.spl -> std.blink.entity.paint_artifact.
- test/unit/lib/crypto/crypto_reference_spec.spl -> std.signature.key_ops
- test/unit/lib/std/common/collection_helpers_spec.spl -> std.collection_helpers.
- test/unit/lib/std/compiler/loader/jit_instantiator_spec.spl -> std.test.spipe.
- test/unit/lib/std/file/file_io_spec.spl -> std.file.
- test/unit/lib/std/game_engine/effects_spec.spl -> std.game_engine.effects.
- test/unit/lib/std/parser/error_recovery_spec.spl -> std.parser.error_recovery.
- test/unit/lib/text/text_index_slice_spec.spl -> std.lib.common.text.adapters,std.lib.common.text.text,std.lib.common.text.text_view
- test/unit/lib/text/text_length_spec.spl -> std.lib.common.text.adapters,std.lib.common.text.text
- test/unit/lib/text/text_search_spec.spl -> std.lib.common.text.adapters,std.lib.common.text.text
- test/unit/std/module_import_spec.spl -> std.test.helpers
- test/unit/std/parser/treesitter_node_spec.spl -> std.parser.treesitter_node.

## Triage update (2026-08-08, second pass)

**Fixed (landed `ba2fab534dfca31d4cd3b62cf7fc84f8c4b9f21e`):** all 28 `std.lib.*`
prefix-typo imports (10 unique spec basenames x2 for the `test/unit` +
`test/01_unit` duplication) corrected to `std.*`. Only
`test/{01_unit,unit}/lib/cc/property_tree_spec.spl` became fully clean by this
fix alone (its sole import was the typo, and `src/lib/cc/entity/property_tree.spl`
genuinely exists). The other 9 basenames (hit_test, paint_chunk,
paint_tree_walker, style_cascade, layer_base, tile, text_index_slice,
text_length, text_search) had the typo fixed but remain broken — they also
import genuinely-unlanded `blink.*`/`common.text.*` submodules. **Correction to
this doc's original subclass-2 framing:** "28 imports where `std.<X>` does
exist" was true for only 3 of 8 unique module strings after stripping `lib.`
(`skia.entity.geometry`, `skia.entity.color`, `cc.entity.property_tree`); the
other 5 (`cc.entity.{layer_base,tile}`, `common.text.{text,adapters,text_view}`)
don't exist under either prefix.

**The original 122/68 figure was an undercount, not a ceiling.** Re-deriving
independently (enumerate every `use std.*` in every `*_spec.spl` on
`origin/main` directly via `git archive`, not by re-checking this doc's own
list) with a resolver that models: direct `src/lib/<path>`, the 9 real
execution-model tiers (`{nogc,gc}_{sync,async}_{mut,immut}` +
`nogc_async_mut_noalloc` — the original calibration's tier list omitted the
four `*_immut` tiers and `gc_sync_mut`), an interior `src/` segment, `.spl` /
`mod.spl` / `__init__.spl` forms, bare-package-directory imports (a directory
with no index file, e.g. `src/lib/common/yaml/`), and single-symbol dotted
imports (`use std.mod.path.Symbol` with no `{}` — must retry with the last
segment dropped, but **only** against file forms, never a bare directory, or
this reintroduces the exact "truncation matches a bare tier dir" failure mode
this doc's first draft had) finds:

    352 flagged spec paths, 202 unique basenames (vs. this doc's 122 / 68)

Calibration (both directions, 10 known-good / 8 known-bad, including the two
edge cases that produced false results during iteration —
`atom` under the immut tiers, and `blink.zzz_fake` which a naive
symbol-drop+bare-dir combination wrongly resolved True): all 18 correct.
Resolver + inputs: cross-check via `git ls-tree -r --name-only origin/main --
src/lib` and `git archive origin/main` (no shared-WC dependency).

**Subclass-1 triage, partial (budget-limited — not all 202 basenames triaged
individually):**
- `blink.*`, `cc.{layer_base,tile}`, `common/text/*`: the shared WC (`git
  status --porcelain -- src/lib`, ~7,595 pending paths) carries partial
  in-flight work for these families (`src/lib/blink/{css_parser,dom}/*`,
  `src/lib/cc/entity/property_tree.spl` already landed). Per this task's
  instruction not to land another session's WC-only files, these are left as
  genuinely in-flight and NOT deleted. `text_length_spec.spl` self-documents
  as an intentional Phase-5 red-phase contract.
- `parser.treesitter*`: `git log origin/main --diff-filter=D --name-only --
  '*treesitter*'` returns empty — never existed, never deleted on mainline
  history. Consistent with planned/red-phase work, not orphaned. Left as-is.
- `bare.hal.*` and the remaining ~190 unique basenames: **not individually
  triaged this pass** — flagging as follow-up work, one pass per top-level
  cluster (blink/cc/parser/crypto/math/game_engine/etc.), each needing the
  same WC-presence + deletion-history check applied above before any delete
  decision.

**Guard viability:** still not viable as a zero-threshold gate — 350 of 352
flagged imports remain (only the property_tree fix is clean). A grandfathered
guard (fail only on *new* `std.*` imports not already in a pinned baseline
list of the current 352) is viable now; the baseline should be regenerated
from the corrected resolver above, not the original 122.

## Triage update (2026-08-08, third pass — the ~190 remaining basenames)

**The 352/202 figure was itself wrong, in the other direction this time.**
Rebuilding the resolver from scratch against a pristine `git archive
origin/main` extraction (never the shared WC) and re-injection-testing it
found two more resolver defects the second pass's own 18/18 calibration did
not catch:

1. **Variable-reuse bug**: the second draft's tier-fallback loop re-bound a
   loop variable (`cand`) across nested loops in a way that leaked a stale
   value from a prior iteration into the bare-directory check, producing
   nondeterministic false positives. Rewritten as a pure candidate-list
   builder (`candidates_direct` + explicit tier prepending), no shared mutable
   state across iterations.
2. **Missing `common` implicit root**: `src/lib/common/` is *itself* an
   implicit search root exactly parallel to the nine execution-model tiers —
   `std.json`, `std.error`, `std.unicode_math`, `std.cert.x509_typed`,
   `std.contracts.contracts`, `std.math.bignum.bignat`, `std.encoding.bson`,
   `std.sdn.value.SdnValue` etc. all resolve via `src/lib/common/<path>`, not
   a top-level `src/lib/<path>`. Neither prior pass modeled this, which alone
   explains ~15 of the "missing" clusters in the second pass's un-itemized
   352 (`math`, `encoding`, `js`, `json`, `convert`, `unicode_math`, `sdn`,
   `error`, `window_protocol`, `text_advanced`, `string_builder`, `result`,
   `result_ce`, `option`, `option_ce`, `format`, `computation`, `cert`,
   `algorithm_utils`, `contracts` — all false positives from the second pass).
3. **Numeric-prefix directories are a real, load-bearing convention**: several
   `src/lib` subtrees order their children with a `NN.` prefix (e.g.
   `src/lib/editor/00.common/`, `src/lib/editor/70.backend/` — the same
   convention `.claude/rules/structure.md` documents for `src/compiler/`'s
   00-99 numbered layers). `use std.editor.backend.gui_backend` legitimately
   resolves to `editor/70.backend/gui_backend.spl`. This single fix cleared
   the entire "editor" cluster (46 flagged paths in the second pass) to zero.

**Corrected, injection-tested count: 162 flagged spec paths, 85 unique
basenames** (vs. the second pass's 352/202 — the drop is ~all resolver
false-positives, not new fixes; only the already-landed `property_tree` fix
changed real content). Calibration: 22/22 both directions (11 known-good
including `std.editor.backend.gui_backend`, `std.math.bignum.bignat`,
`std.atom` under the immut tiers, and 11 known-bad including
`std.blink.zzz_fake`, `std.bare.hal.gpio`, `std.parser.treesitter`). Resolver:
`/tmp/spectriage/resolve.py` (scratch, not committed — reproducible from
`git archive origin/main` + the tier/common/numeric-prefix rules above).

Cluster breakdown of the corrected 162/85:

    gc_async_mut 66 | blink 66 | common 21 | cc 20 | parser 14 | nogc_async_mut 12
    bare 10 | tooling 6 | debug 6 | sys 5 | test 4 | system 4 | spec 2 | signature 2
    probability_utils 2 | plugin 2 | nogc_sync_mut 2 | game_engine 2 | file 2
    ds_utils 2 | diagnostics 2 | collection_helpers 2 | prelude 1 | doctest 1 | app 1

**Deletion-history check, all 85 basenames' top-level namespaces:** `git log
origin/main --diff-filter=D --name-only -- <path>` returns **empty for every
single one** checked (`bare/hal`, `sys`, `signature`, `probability_utils`,
`plugin`, `game_engine`, `file`, `ds_utils`, `diagnostics`, `collection_helpers`,
`prelude`, `doctest`, `app`, `test/helpers`, `tooling/compiler`, `debug/remote`,
plus the previously-checked `blink`, `cc`, `parser.treesitter`, and the new
`gc_async_mut.{database,compression,dap,fs*}` clusters). **None of the 352
flagged imports point at code that was ever landed and later removed.** Every
one is consistent with planned/red-phase work that was never landed, the same
pattern already established for `parser.treesitter*`.

**Decision: leave, do not delete, do not land.** Given (a) zero deletion
history anywhere in the set, (b) the explicit instruction not to land
another session's WC-only work to justify a spec, and (c) a WC-presence
check (tightened to require an exact `src/lib/<matched-prefix>/...` path,
not a loose same-tier-directory match — the loose version wrongly "matched"
unrelated siblings like `common.engine.signal.event_bus` against
`common/engine/audio/...`) found only 5 of 141 unique bad module strings with
any tight WC match (`common.engine.signal.event_bus`, `common.math.field.*`,
`common.svmg.ref_vm`, `nogc_sync_mut.src.tooling.regex_utils`) — not enough
to justify landing anything, and not enough to prove the rest are orphaned
either. **None of the remaining 85 basenames were individually triaged to a
delete/land verdict this pass** — the evidence available (no deletion
history + thin WC signal) points to "leave as planned/red-phase," same
verdict for effectively the whole set, so no specs were deleted and no
modules were landed in this pass.

**Harness spot-check:** attempted to confirm via `bin/simple test` on
`test/01_unit/lib/crypto/crypto_reference_spec.spl` (content-identical to
`origin/main`, verified by blob hash) but the run did not complete within the
available time budget (shared machine, concurrent sessions running other
long specs). Not used as evidence either way; the file-existence resolver
(injection-tested 22/22) is the primary oracle here, consistent with how the
first pass validated the `hash` facade.

**Guard viability, restated:** still not a zero-threshold gate (162 of ~254
imports checked still flag). A grandfathered guard is viable at the
corrected 162/85 baseline. **Not landed this pass** — regenerating and
pinning a baseline now would freeze the count I could not fully individually
triage; leaving that to a follow-up pass that either lands it as a proper
baseline file or explicitly re-derives at triage-complete time.

**Not landed:** no code changes this pass beyond this doc update. No specs
deleted, no modules landed, no guard script added.

