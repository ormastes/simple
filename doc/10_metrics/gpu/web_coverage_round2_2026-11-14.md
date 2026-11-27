# Simple web coverage, round 2 — measured 2026-11-14

Continues `doc/10_metrics/gpu/render_coverage_2026-11-14.md` (PR #9103), which
has the method and the Simple 2D numbers. Scope here:
`src/lib/gc_async_mut/gpu/browser_engine/**` (181 files). Tree:
`origin/release/1.0.0` @ `ec758ee501c` + branch `work/render-coverage-web-2-20261114`.

## Result

| | lines | decisions (both outcomes) |
|---|---|---|
| round 1 (PR #9103) | 30162/38911 = 77.5% | 6950/12652 = 54.9% |
| round 2 | 32025/38911 = 82.3% | 7515/12681 = 59.3% |
| still missing for 90% | 2995 lines | 3898 decisions |

Still interpreter-only and a lower bound. **90% was not reached.**

Where the +4.8 points came from

1. **Scorer fix** (`src/lib/common/coverage_module_report.spl`): a method
   written `me fn name(...)` was read as a function called `fn`, so every line
   of such methods scored as never called. Eight browser_engine files use that
   form; `net/cookie_store.spl` went from 38.3% to 93.6% on the same artifact.
   Round 1's 77.5% was under-reported by this.
2. **61 of the 91 specs round 1 could not sweep** (`test/03_system` tail incl.
   the web_platform WebGL / WebGPU specs, `test/05_perf`). The last 30
   (`test/feature`, `test/system` mirrors and 3 perf specs) are still unswept.
3. **9 new spec files** (below).

## Calibration added in this round

A second hand-countable fixture (multi-line constructor literal, multi-line
call, early returns, tail expressions; every function executed) scores
`lines=100.0% (5/5) decisions=100.0% (2/2)`: the denominator is only the
statement kinds the collector records (`val`/`var`/`if`/`while`/`for`/`return`/
`match`/assignments). Bare call statements, tail expressions and continuation
lines are in neither numerator nor denominator, so nothing is unreachable by
construction — but a function that is one tail expression contributes 0 lines.

## Limits specific to this round

- 12 files changed on `release/1.0.0` after the round-1 sweep (the
  `simple_web_html_layout_renderer_*` family, another lane's work). The scorer
  refuses artifacts recorded against a different source version, so their rows
  below are **carried from round 1** and are stale. `selector_matcher.spl` and
  `script/js_compat.spl` were changed by this branch and are carried too.
- Only files touched by the new specs were re-scored after the full re-score;
  the others keep the full re-score value.

## What blocks 90% (6,886 uncovered lines; 2,995 more hits needed)

| bucket | uncovered | note |
|---|---:|---|
| `simple_web_html_layout_renderer_*` + `simple_web_fractional_box_resolver` | 1,728 | active layout/paint lane, stale rows; needs a re-sweep after that lane lands |
| `js/` (lexer, parser, interpreter, dom_bridge) | 846 | no importer in `src/`; interpreter mis-evaluates basic programs — owner decision: delete or repair (bug filed) |
| WebGL / WebGPU | ~770 | reachable: remaining error branches (texture upload, framebuffer, `*_with_resources` validators) |
| `net/` | ~670 | reachable for parsers; `websocket_client`, `tls`, `h1_client` socket paths need a loopback harness; HTTP/2 is blocked by the high-octet bug |
| `gpu_web/**` CUDA ports | 232 | host has no CUDA lane |
| rest (dom_accessors 249, style_rule_index 227, dom_color, script/*, layout_core, …) | ~2,640 | reachable with CPU specs |

Removing `js/` and the CUDA ports from the denominator would put the current
tree at about 84.6%. Reaching 90% without that needs roughly 25 more spec
files of the size written here plus a re-sweep of the layout renderer family.

## Specs added (9 new files, 185 examples) and fixes

| spec (test/01_unit/lib/gc_async_mut/gpu/browser_engine/) | examples |
|---|---:|
| dom_form_owner_and_child_mutation_spec | 23 |
| style_rule_index_lookup_spec | 22 |
| js_values_heap_spec | 17 |
| webgpu_device_lifecycle_free_api_spec | 25 |
| h2_settings_and_header_block_spec | 21 |
| dns_cache_and_ws_handshake_spec | 23 |
| webgl_uniform_and_sampler_errors_spec | 17 |
| webgl_draw_and_object_errors_spec | 16 |
| cors_safelist_and_uri_component_spec | 21 |
| (test/01_unit/lib/common/) coverage_module_report_spec, +1 example | 1 |

Source fixes, each red -> green in this branch

- `selector_matcher.spl`: `:nth-child(...)` matched every sibling (the matcher was `selector.contains(":nth-child")`). Now evaluates integer / odd / even / An+B. Red 16/22, green 22/22; `browser_renderer_spec` 129/130 -> 130/130.
- `script/js_compat.spl`: `encodeURIComponent` left `%` (and `" < > \ ^ \` |`) unescaped and escaped `! * ' ( )`; `decodeURIComponent` only knew 19 escapes (`%41` stayed `%41`). Red 15/17, green 21/21.
- `common/coverage_module_report.spl`: the `me fn` naming bug above. Red 24/25, green 25/25.

Mutation checks (edit, red, revert): WebGPU `present_count += 2` -> 1 example red; DNS `is_expired` `>` -> `>=` -> 3 examples red.

Bugs filed, not fixed (`doc/08_tracking/bug/`)

- `js_engine_interpreter_wrong_results_2026-11-14.md` — `var x = 5; x = x + 1;` yields 1; programs with a function call end the host process silently with exit 0.
- `h2_text_carrier_loses_high_octets_2026-11-14.md` — every octet >= 0x80 is lost: a 200-octet DATA frame decodes with length 0 and the default 65535 window encodes as 0.

Observed, not asserted: `WebGLContext.get_error()` keeps returning CONTEXT_LOST_WEBGL on a lost context; the WebGL spec says only the first call does.

## Per file (sorted by uncovered executable lines)

| file (under browser_engine/) | exec | hit round 1 | hit round 2 | line % | decision % | note |
|---|---:|---:|---:|---:|---:|---|
| webgl_context.spl | 2503 | 1918 | 2079 | 83.1 | 61.5 |  |
| js/parser.spl | 360 | 0 | 0 | 0.0 | n/a | never loaded |
| simple_web_fractional_box_resolver.spl | 300 | 0 | 0 | 0.0 | 0.0 |  |
| js/interpreter.spl | 258 | 0 | 0 | 0.0 | n/a | never loaded |
| dom_accessors.spl | 921 | 583 | 672 | 73.0 | 53.9 |  |
| simple_web_html_layout_renderer_foundation.spl | 1639 | 1408 | 1408 | 85.9 | 60.2 |  |
| style_rule_index.spl | 576 | 232 | 349 | 60.6 | 26.8 |  |
| simple_web_html_layout_renderer.spl | 1039 | 837 | 837 | 80.6 | 46.2 | carried |
| simple_web_html_layout_renderer_layout_foundation.spl | 1018 | 818 | 818 | 80.4 | 61.5 | carried |
| simple_web_html_layout_renderer_layout_engine.spl | 1297 | 1101 | 1101 | 84.9 | 58.7 | carried |
| web_opaque_box_qualification.spl | 329 | 144 | 144 | 43.8 | 12.6 |  |
| js/lexer.spl | 184 | 0 | 0 | 0.0 | n/a | never loaded |
| gpu_web/layout/cuda_execution_port.spl | 169 | 0 | 0 | 0.0 | 0.0 |  |
| simple_web_html_layout_renderer_paint_raster.spl | 897 | 737 | 737 | 82.2 | 50.0 | carried |
| net/h1_client.spl | 581 | 427 | 432 | 74.4 | 47.9 |  |
| webgpu_context.spl | 800 | 421 | 653 | 81.6 | 62.7 |  |
| style/supports.spl | 355 | 215 | 215 | 60.6 | 32.2 |  |
| simple_web_html_layout_renderer_core_selectors.spl | 1615 | 1477 | 1477 | 91.5 | 75.4 |  |
| web_corpus_case02_projection.spl | 129 | 0 | 0 | 0.0 | 0.0 |  |
| simple_web_layout_engine2d_fast.spl | 384 | 274 | 274 | 71.4 | 38.1 |  |
| script/js_transpiler.spl | 373 | 271 | 271 | 72.7 | 41.9 |  |
| net/websocket_client.spl | 99 | 0 | 0 | 0.0 | n/a | never loaded |
| simple_web_engine2d_renderer.spl | 659 | 566 | 566 | 85.9 | 58.1 |  |
| webgpu_commands.spl | 501 | 151 | 409 | 81.6 | 61.6 |  |
| dom_color.spl | 539 | 458 | 458 | 85.0 | 33.6 |  |
| web_render_backend.spl | 93 | 6 | 13 | 14.0 | 9.5 |  |
| widget_to_dom.spl | 273 | 199 | 199 | 72.9 | 44.7 |  |
| simple_web_html_layout_renderer_paint_layout.spl | 791 | 718 | 718 | 90.8 | 64.6 | carried |
| net/dns.spl | 161 | 62 | 91 | 56.5 | 30.8 |  |
| script/js_compat.spl | 301 | 235 | 235 | 78.1 | 47.8 |  |
| layout_core.spl | 81 | 18 | 18 | 22.2 | 16.7 |  |
| simple_web_html_layout_renderer_core.spl | 788 | 726 | 726 | 92.1 | 71.1 | carried |
| script/script_host.spl | 91 | 34 | 34 | 37.4 | 24.1 |  |
| net/h2_client.spl | 53 | 0 | 0 | 0.0 | n/a | never loaded |
| net/tls.spl | 80 | 29 | 29 | 36.2 | 28.6 |  |
| style/animation_controller.spl | 50 | 0 | 0 | 0.0 | n/a | never loaded |
| simple_web_html_layout_renderer_style.spl | 794 | 747 | 747 | 94.1 | 76.7 |  |
| paint.spl | 174 | 130 | 130 | 74.7 | 27.3 |  |
| simple_web_html_engine2d_presenter.spl | 381 | 337 | 337 | 88.5 | 58.0 |  |
| dom.spl | 205 | 162 | 162 | 79.0 | 53.0 |  |
| js/dom_bridge.spl | 42 | 0 | 0 | 0.0 | n/a | never loaded |
| layout_table.spl | 328 | 286 | 286 | 87.2 | 67.0 |  |
| simple_web_html_layout_renderer_core_css_rules.spl | 590 | 548 | 548 | 92.9 | 71.8 |  |
| html_tokenizer.spl | 420 | 379 | 379 | 90.2 | 83.2 |  |
| script/canvas_api.spl | 645 | 605 | 605 | 93.8 | 22.0 |  |
| browsing_context.spl | 108 | 6 | 69 | 63.9 | 57.9 |  |
| net/h2_hpack.spl | 111 | 18 | 72 | 64.9 | 53.1 |  |
| style/custom_properties.spl | 142 | 104 | 104 | 73.2 | 41.9 |  |
| webgpu_resources.spl | 309 | 160 | 271 | 87.7 | 69.5 |  |
| html_string_parser.spl | 176 | 139 | 139 | 79.0 | 43.2 |  |
| security/origin_policy.spl | 280 | 240 | 243 | 86.8 | 66.1 |  |
| text_painter.spl | 241 | 191 | 204 | 84.6 | 50.0 |  |
| webgpu_software_executor.spl | 204 | 89 | 169 | 82.8 | 48.3 |  |
| browser_renderer.spl | 73 | 43 | 43 | 58.9 | 72.7 |  |
| simple_web_html_layout_renderer_paint_primitives.spl | 1030 | 1001 | 1001 | 97.2 | 85.5 |  |
| net/ws_frame_codec.spl | 133 | 105 | 105 | 78.9 | 71.0 |  |
| script/simple_script.spl | 85 | 57 | 57 | 67.1 | 30.8 |  |
| gpu_web/layout/adapter.spl | 145 | 118 | 118 | 81.4 | 61.3 |  |
| net/ws_handshake.spl | 89 | 46 | 63 | 70.8 | 53.6 |  |
| dom_identity_index.spl | 230 | 205 | 205 | 89.1 | 69.9 |  |
| layout_box.spl | 24 | 0 | 0 | 0.0 | n/a | never loaded |
| web_opaque_box_checks.spl | 69 | 46 | 46 | 66.7 | 39.4 |  |
| glass_comparison_runner.spl | 96 | 11 | 74 | 77.1 | 45.2 |  |
| security/cookie_policy.spl | 194 | 172 | 172 | 88.7 | 62.5 |  |
| simple_web_css_box_effects.spl | 283 | 261 | 261 | 92.2 | 71.3 |  |
| chrome_webgpu_draw_evidence.spl | 106 | 86 | 86 | 81.1 | 40.0 |  |
| net/cookie_store.spl | 316 | 121 | 296 | 93.7 | 77.4 |  |
| net/fetch.spl | 202 | 179 | 182 | 90.1 | 61.8 |  |
| script/location_api.spl | 59 | 39 | 39 | 66.1 | 33.3 |  |
| simple_web_html_layout_renderer_declarations.spl | 1062 | 1043 | 1043 | 98.2 | 81.7 | carried |
| simple_web_render_session.spl | 121 | 95 | 102 | 84.3 | 50.0 |  |
| chrome_webgpu_compute_evidence.spl | 93 | 78 | 78 | 83.9 | 50.0 |  |
| gpu_web/text/cuda_line_break.spl | 99 | 85 | 85 | 85.9 | 29.3 |  |
| net/cache.spl | 105 | 91 | 91 | 86.7 | 48.6 |  |
| net/ws_utils.spl | 134 | 113 | 120 | 89.6 | 50.0 |  |
| script/dom_api.spl | 96 | 82 | 82 | 85.4 | 55.2 |  |
| script/form_api.spl | 56 | 42 | 42 | 75.0 | 63.0 |  |
| style/animation.spl | 136 | 122 | 122 | 89.7 | 37.8 |  |
| browser_renderer_utils.spl | 263 | 250 | 250 | 95.1 | 74.1 |  |
| layout.spl | 186 | 173 | 173 | 93.0 | 72.4 |  |
| net/h2_stream.spl | 13 | 0 | 0 | 0.0 | n/a | never loaded |
| style_block_parse.spl | 486 | 473 | 473 | 97.3 | 81.7 |  |
| net/cors.spl | 170 | 72 | 158 | 92.9 | 76.4 |  |
| script/script_runner.spl | 33 | 21 | 21 | 63.6 | 0.0 |  |
| style/computed.spl | 12 | 0 | 0 | 0.0 | n/a | never loaded |
| browser_script_execute.spl | 181 | 170 | 170 | 93.9 | 75.0 |  |
| gpu_web/dom/dom_arena_types.spl | 98 | 87 | 87 | 88.8 | 60.0 |  |
| script/worker_api.spl | 23 | 12 | 12 | 52.2 | 33.3 |  |
| simple_web_html_layout_renderer_decl_apply.spl | 2008 | 1997 | 1997 | 99.5 | 69.5 | carried |
| simple_web_html_layout_renderer_geometry.spl | 139 | 128 | 128 | 92.1 | 63.0 | carried |
| web_paint_chunk_frame.spl | 112 | 101 | 101 | 90.2 | 48.1 |  |
| selector_matcher.spl | 86 | 76 | 76 | 88.4 | 56.0 | carried |
| backend_screenshot_capture.spl | 84 | 75 | 75 | 89.3 | 28.6 |  |
| browser_script_render.spl | 79 | 70 | 70 | 88.6 | 45.0 |  |
| net/h2_frame.spl | 305 | 229 | 296 | 97.0 | 25.0 |  |
| security/permission_policy.spl | 84 | 27 | 75 | 89.3 | 68.0 |  |
| style/render_state.spl | 9 | 0 | 0 | 0.0 | n/a | never loaded |
| net/entity/url_types.spl | 44 | 36 | 36 | 81.8 | 65.0 |  |
| rendering_parity_adapter.spl | 82 | 74 | 74 | 90.2 | 42.1 |  |
| style/transform.spl | 103 | 95 | 95 | 92.2 | 76.7 |  |
| gpu_web/dom/dom_arena_build.spl | 139 | 132 | 132 | 95.0 | 87.5 |  |
| html_tree_builder.spl | 362 | 355 | 355 | 98.1 | 58.5 |  |
| simple_web_layout_engine2d_cpu.spl | 27 | 19 | 20 | 74.1 | 20.0 |  |
| style_block_resolve.spl | 321 | 314 | 314 | 97.8 | 86.8 |  |
| web_showcase_tabs.spl | 37 | 30 | 30 | 81.1 | 43.8 |  |
| layout_float.spl | 122 | 116 | 116 | 95.1 | 69.2 |  |
| render_fixtures.spl | 302 | 296 | 296 | 98.0 | 61.4 |  |
| simple_web_file_renderer.spl | 44 | 38 | 38 | 86.4 | 46.2 |  |
| script/event_loop.spl | 48 | 43 | 43 | 89.6 | 77.8 |  |
| simple_web_html_layout_renderer_paint_tiles_gpu.spl | 101 | 96 | 96 | 95.0 | 52.4 |  |
| style_invalidation.spl | 105 | 100 | 100 | 95.2 | 68.6 |  |
| style_property_id.spl | 97 | 92 | 92 | 94.8 | 80.0 |  |
| dom_visual_effects.spl | 97 | 93 | 93 | 95.9 | 58.6 |  |
| web_draw_ir_damage_consumer.spl | 20 | 16 | 16 | 80.0 | 60.0 |  |
| dom_color_named.spl | 127 | 124 | 124 | 97.6 | 86.7 |  |
| glass_pipeline_compare.spl | 32 | 0 | 29 | 90.6 | 100.0 |  |
| net/entity/cookie_types.spl | 3 | 0 | 0 | 0.0 | n/a | never loaded |
| simple_web_box_geometry_provenance.spl | 79 | 76 | 76 | 96.2 | 82.1 |  |
| simple_web_url_placeholder_renderer.spl | 14 | 11 | 11 | 78.6 | 20.0 |  |
| gpu_web/layout/manager.spl | 24 | 22 | 22 | 91.7 | 71.4 |  |
| js/values.spl | 73 | 0 | 71 | 97.3 | 86.4 |  |
| net/ws_crypto.spl | 160 | 158 | 158 | 98.8 | 91.1 |  |
| resource_loader.spl | 33 | 31 | 31 | 93.9 | 76.9 |  |
| simple_web_corpus_fixture_renderer.spl | 26 | 21 | 24 | 92.3 | 28.6 |  |
| simple_web_html_layout_renderer_paint_tiles.spl | 164 | 162 | 162 | 98.8 | 94.6 |  |
| webgpu_status_errors.spl | 29 | 5 | 27 | 93.1 | 88.9 |  |
| gpu_web/layout/cpu_execution_port.spl | 49 | 48 | 48 | 98.0 | 23.5 | carried |
| gpu_web/layout/invalidation.spl | 16 | 15 | 15 | 93.8 | 50.0 |  |
| layout_paint.spl | 9 | 8 | 8 | 88.9 | 66.7 |  |
| net/fetch_dispatch.spl | 2 | 1 | 1 | 50.0 | n/a |  |
| script/clipboard_api.spl | 7 | 6 | 6 | 85.7 | 50.0 |  |
| script/event_api.spl | 47 | 46 | 46 | 97.9 | 11.1 |  |
| script/navigator_api.spl | 3 | 2 | 2 | 66.7 | n/a |  |
| script/network_api.spl | 54 | 53 | 53 | 98.1 | 75.0 |  |
| simple_web_ssr_renderer.spl | 1 | 0 | 0 | 0.0 | n/a | never loaded |
| style_block.spl | 308 | 307 | 307 | 99.7 | 90.7 |  |
| web_decimal_geometry_diagnostic.spl | 3 | 2 | 2 | 66.7 | 0.0 |  |
| browser_engine2d_bridge.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| browser_file_ops.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| containment.spl | 32 | 32 | 32 | 100.0 | 87.5 |  |
| css.spl | 12 | 12 | 12 | 100.0 | 100.0 |  |
| dom_limits.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| glass_demo_registry.spl | 8 | 0 | 8 | 100.0 | 100.0 |  |
| gpu_web/dom/__init__.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| gpu_web/__init__.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| gpu_web/layout/contracts.spl | 39 | 39 | 39 | 100.0 | 100.0 |  |
| gpu_web/layout/__init__.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| gpu_web/text/__init__.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| html_fallback_renderer.spl | 234 | 234 | 234 | 100.0 | 82.7 |  |
| html_named_character_references.spl | 10 | 10 | 10 | 100.0 | 100.0 |  |
| js/ast.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| layout_inline.spl | 38 | 38 | 38 | 100.0 | 100.0 |  |
| layout_insets.spl | 8 | 8 | 8 | 100.0 | 100.0 |  |
| layout_m14_types.spl | 10 | 10 | 10 | 100.0 | 100.0 |  |
| mod.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| net/browser_trust_store.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| net/entity/cache_types.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| net/entity/cors_types.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| net/entity/request_types.spl | 4 | 1 | 4 | 100.0 | 100.0 |  |
| net/entity/tls_types.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| net/h2_settings.spl | 29 | 0 | 29 | 100.0 | 100.0 | carried |
| net/net_delegate.spl | 3 | 1 | 3 | 100.0 | n/a |  |
| script/console_api.spl | 25 | 25 | 25 | 100.0 | 100.0 |  |
| script/console_buffer.spl | 15 | 15 | 15 | 100.0 | 100.0 |  |
| script/js_simple_matrix.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| script/mod.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| script/storage_api.spl | 24 | 24 | 24 | 100.0 | 85.7 |  |
| script/timer_api.spl | 4 | 4 | 4 | 100.0 | n/a |  |
| shared/error.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| shared/logging.spl | 5 | 5 | 5 | 100.0 | 100.0 |  |
| simple_web_css_property_id.spl | 15 | 15 | 15 | 100.0 | 97.3 |  |
| simple_web_html_layout_renderer_core_types.spl | 27 | 27 | 27 | 100.0 | 80.0 |  |
| simple_web_html_layout_renderer_layout.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| simple_web_html_renderer.spl | 7 | 7 | 7 | 100.0 | 100.0 |  |
| simple_web_renderer.spl | 1 | 1 | 1 | 100.0 | n/a |  |
| simple_web_script_placeholder_renderer.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| simple_web_script_renderer.spl | 8 | 8 | 8 | 100.0 | 100.0 |  |
| webgl_render_commands.spl | 8 | 8 | 8 | 100.0 | 81.8 |  |
| webgpu_types.spl | 0 | 0 | 0 | n/a | n/a | never loaded |
| web_renderable_feature_inventory.spl | 95 | 95 | 95 | 100.0 | 100.0 |  |
| web_renderable_feature_witness.spl | 92 | 92 | 92 | 100.0 | 95.3 |  |
