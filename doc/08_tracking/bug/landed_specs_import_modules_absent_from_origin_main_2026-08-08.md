# Landed specs import modules absent from origin/main (2026-08-08)

**Status:** open — family enumerated, not yet triaged.

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
- test/unit/app/svllm_pack/main_spec.spl -> std.app.svllm_pack.main.
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
