# Duplicate test-tree merge worklist (legacy vs numbered) — REDERIVED

**Status:** OPEN — analysis only, no merges in this revision
**Original:** 2026-08-09 stream I4 · **Triage:** 2026-08-10 stream J4 · **Re-derived:** 2026-08-10 stream M4
**Component:** `test/**`
**Measured against:** `origin/main` @ `46baea155f8` (NOT the dirty working copy)

## ⚠ THE RAW-LINE-COUNT RANKING IS SUPERSEDED — DO NOT WORK FROM IT

The original worklist ranked pairs by **raw line count** and listed 145 files as
"legacy ahead". That metric counts commented-out bodies. Stream J4 verified 6
merges and disproved the premise; this revision re-derives everything on a
**code-line** metric with a pending/disabled-marker filter.

The flagship example of the old ranking, `test/unit/app/diagram/filter_spec.spl`
(199 raw lines vs an 11-line numbered twin), is **4 code lines** — an
`it "skipped"` stub with 195 lines of dead comments. Merging it would have been a
regression. That entry, and 60 others like it, are now closed unmerged.

## Metric (and its control)

- **code lines** = lines that are non-blank and whose first non-space character
  is not `#` (`.spl` comment syntax). Full-line comments only; no attempt to
  strip trailing comments, which would risk cutting `#` inside string literals.
- **pending/disabled markers**, derived from the corpus rather than assumed. Of
  the candidate markers tested (`it "skipped|pending|disabled|TODO"`,
  `pending_reason`, `xit`/`xdescribe`/`it_skip`, `skip(`, `pending(`), only three
  actually occur in the divergent corpus: `it "skipped…"` (193 legacy-side hits),
  `pending_reason` (189), `pending(` (2). `xit`/`xdescribe`/`skip(` occur **zero**
  times — they are not this corpus's idiom. The first two nearly always co-occur.
- **Control:** `filter_spec.spl` measures 199 raw / **4 code**, marker-positive —
  reproducing J4's hand count exactly. The stripper is trusted on that basis.

## Re-derived census (origin/main, 1046 divergent pairs)

| ranking | count |
|---|---|
| raw lines: legacy ahead | 133 |
| raw lines: equal but different | 355 |
| raw lines: numbered ahead | 558 |
| **code lines: legacy ahead** | **78** |
| raw-ahead but NOT code-ahead (**DISPROVEN**) | 61 |
| …of those, legacy is pending/disabled-marked | 51 |

The 133/355/558 differ slightly from I4's 145/364/571 because six pairs were
merged to identity by J4 (they no longer diverge), eight were reverted to
identity, and this pass de-duplicates `test/03_system/feature` against
`test/03_system` so no pair is counted under two roots.

**Expected 145 → ~81 was approximately right, and is now measured: 78.**
Of the 133 raw-ahead entries, **72 survive** the code-line metric and **61 are
disproven**. The extra 6 in the code-ahead list are pairs where legacy was
raw-shorter or raw-equal yet has more real code — invisible to the old ranking.

## Classification

Applied in this order (first match wins):

| class | rule | action |
|---|---|---|
| `stub-legacy` | legacy carries a pending/disabled marker and numbered does not | **close unmerged** |
| `stale-use-only` | every legacy-only code line is a `use …` import | **close unmerged** (restoring it makes the spec fail to load: exit 1, no verdict line — J4 FINDING 3) |
| `genuine-merge` | legacy is a strict code superset (numbered contributes zero unique code lines) | real work — merge and verify |
| `style-difference` | both sides carry unique code lines | needs the two-way read |

### Counts — code-line legacy-ahead (78)

| class | count |
|---|---|
| genuine-merge | 2 |
| stale-use-only | 7 |
| style-difference | 69 |
| stub-legacy | 0 |

`style-difference` dominates. That is the honest answer, not a failure of the
classifier: J4 FINDING 4 showed short numbered twins are frequently a different
test *style* (source-grep API-presence) rather than placeholders, and the legacy
behavioural twin is sometimes the dead one. The `uniq num/leg` columns below are
the triage lever — an entry with `uniq_num` of 1-2 is usually a renamed
`describe` header plus real added legacy content and merges cleanly; an entry
with `uniq_num` in double digits is a genuine rewrite where the numbered side is
the newer intent.

### Counts — equal-raw-length pairs (355), never previously triaged

| class | count |
|---|---|
| genuine-merge | 41 |
| stale-use-only | 29 |
| style-difference | 285 |
| stub-legacy | 0 |

Same raw length, different content — confirmed for all 355. 29 of them
differ **only** by an import line (a swap, not an addition), and 41 are legacy
code-supersets at equal raw length (legacy trades comments for code). None are
byte-identical, so none can be swept.

## Worklist A — code-line legacy-ahead (78), sorted by code-line delta

| numbered | class | code n/l | raw n/l | uniq num/leg |
|---|---|---|---|---|
| `test/03_system/os_crypto_ref_helpers.spl` | style-difference | 1/241 | 6/311 | 1/188 |
| `test/01_unit/app/llm_caret/server_spec.spl` | style-difference | 81/226 | 112/269 | 9/134 |
| `test/02_integration/app/optimize/optimize_cli_spec.spl` | style-difference | 76/162 | 120/242 | 8/85 |
| `test/01_unit/app/llm_caret/claude_api_spec.spl` | style-difference | 170/253 | 189/293 | 110/215 |
| `test/01_unit/app/ui/backend_matrix_spec.spl` | style-difference | 97/175 | 115/197 | 9/37 |
| `test/01_unit/app/llm_caret/openai_api_spec.spl` | style-difference | 193/263 | 213/300 | 129/223 |
| `test/01_unit/os/installer/image_builder_artifact_spec.spl` | style-difference | 46/115 | 51/124 | 5/59 |
| `test/01_unit/compiler/backend/llvm_ir_builder_spec.spl` | style-difference | 43/104 | 64/152 | 1/57 |
| `test/01_unit/compiler/types/platform_layout_attribute_spec.spl` | style-difference | 125/186 | 156/227 | 67/88 |
| `test/01_unit/os/tls13/server_accept_spec.spl` | style-difference | 563/622 | 751/810 | 14/63 |
| `test/01_unit/os/kernel/memory/vmm_vma_spec.spl` | style-difference | 194/233 | 261/303 | 29/65 |
| `test/02_integration/lib/std/doctest/discovery_spec.spl` | style-difference | 36/73 | 49/91 | 33/60 |
| `test/01_unit/app/tooling/test_runner_simple_spec.spl` | style-difference | 299/333 | 519/571 | 18/43 |
| `test/01_unit/lib/common/zstd_sequence_fse_execution_spec.spl` | style-difference | 368/402 | 401/425 | 46/62 |
| `test/01_unit/compiler/linker/platform_defaults_spec.spl` | style-difference | 129/162 | 170/206 | 61/79 |
| `test/01_unit/lib/common/torch/torch_device_placement_status_spec.spl` | style-difference | 79/101 | 96/117 | 13/30 |
| `test/01_unit/core/parser_ce_keyword_identifier_spec.spl` | style-difference | 85/104 | 92/118 | 1/13 |
| `test/03_system/feature/usage/pass_variants_spec.spl` | style-difference | 120/136 | 153/165 | 83/76 |
| `test/01_unit/os/proxy/stun_spec.spl` | style-difference | 418/433 | 513/528 | 4/5 |
| `test/01_unit/app/test_runner_new/test_config_spec.spl` | style-difference | 47/61 | 66/86 | 7/12 |
| `test/01_unit/app/tooling/command_dispatch_spec.spl` | style-difference | 582/596 | 805/820 | 95/90 |
| `test/05_perf/cli_dispatch_perf_spec.spl` | style-difference | 132/146 | 251/270 | 1/15 |
| `test/03_system/feature/lib/mcp/simple_import_test.spl` | style-difference | 12/25 | 25/39 | 4/14 |
| `test/01_unit/lib/common/mock_phase7_spec.spl` | style-difference | 973/985 | 1156/1174 | 8/18 |
| `test/01_unit/os/kernel/memory/pmm_spec.spl` | style-difference | 121/133 | 186/196 | 3/15 |
| `test/01_unit/std/mock_phase7_spec.spl` | style-difference | 961/973 | 1144/1162 | 8/18 |
| `test/01_unit/lib/skia/canvas_spec.spl` | style-difference | 99/110 | 123/134 | 18/22 |
| `test/01_unit/os/crypto/sm3_kat_spec.spl` | genuine-merge | 157/168 | 190/190 | 0/6 |
| `test/03_system/compiler/driver_api_tier_policy_spec.spl` | style-difference | 241/252 | 309/335 | 8/19 |
| `test/03_system/feature/lib/mcp/handler_import_test.spl` | style-difference | 11/21 | 22/32 | 2/10 |
| `test/01_unit/compiler/parser/pub_enum_with_attribute_spec.spl` | genuine-merge | 20/28 | 36/46 | 0/8 |
| `test/03_system/database/server/db_server_tier_spec.spl` | style-difference | 311/319 | 419/438 | 12/41 |
| `test/01_unit/app/test_runner_new/test_runner_args_ci_spec.spl` | style-difference | 25/32 | 35/44 | 3/9 |
| `test/01_unit/lib/editor/extension_discovery_contract_spec.spl` | style-difference | 72/79 | 92/93 | 28/36 |
| `test/03_system/feature/web_platform/css/transforms_wpt_spec.spl` | style-difference | 104/111 | 125/131 | 77/80 |
| `test/05_perf/bench/jit_minimal_test.spl` | style-difference | 10/17 | 11/23 | 5/12 |
| `test/01_unit/lib/common/zstd_fse_weights_spec.spl` | style-difference | 81/87 | 125/131 | 1/7 |
| `test/01_unit/lib/common/crypto/lshr2_debug_spec.spl` | style-difference | 20/25 | 28/32 | 2/7 |
| `test/01_unit/lib/common/crypto/lshr3_debug_spec.spl` | style-difference | 16/21 | 20/23 | 2/7 |
| `test/01_unit/lib/std/concurrency/concurrency_spec.spl` | style-difference | 446/450 | 574/580 | 2/6 |
| `test/03_system/feature/usage/hm_type_inference_spec.spl` | style-difference | 362/366 | 504/509 | 31/30 |
| `test/03_system/feature/usage/trait_forwarding_spec.spl` | style-difference | 187/191 | 240/245 | 1/5 |
| `test/02_integration/os/port/native_convergence_spec.spl` | style-difference | 42/46 | 59/64 | 2/6 |
| `test/03_system/gui/native_gui_build_spec.spl` | style-difference | 256/260 | 339/344 | 30/34 |
| `test/01_unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl` | style-difference | 213/216 | 285/294 | 29/49 |
| `test/01_unit/lib/nogc_async_mut/concurrent_spec.spl` | style-difference | 162/165 | 227/231 | 2/5 |
| `test/01_unit/lib/nogc_async_mut/http_server/static_file_handler_compression_spec.spl` | style-difference | 138/141 | 180/189 | 18/20 |
| `test/02_integration/examples/platform_library_example_spec.spl` | style-difference | 188/191 | 283/286 | 5/8 |
| `test/01_unit/app/llm_caret/gemini_cli_spec.spl` | style-difference | 316/318 | 406/406 | 2/4 |
| `test/01_unit/compiler/custom_blocks_easy_api_spec.spl` | style-difference | 302/304 | 402/405 | 6/8 |
| `test/01_unit/compiler/linker/lib_smf_writer_spec.spl` | style-difference | 76/78 | 97/100 | 6/8 |
| `test/01_unit/compiler_core/keyof_spec.spl` | style-difference | 14/16 | 21/20 | 1/3 |
| `test/01_unit/lib/nogc_async_mut/http_server/static_file_compression_cache_spec.spl` | style-difference | 126/128 | 158/164 | 16/17 |
| `test/01_unit/os/process_isolation_as_spec.spl` | style-difference | 122/124 | 166/166 | 3/4 |
| `test/01_unit/runtime/process_is_running_spec.spl` | style-difference | 44/46 | 72/72 | 19/24 |
| `test/01_unit/std/mock_phase5_spec.spl` | style-difference | 463/465 | 579/582 | 1/3 |
| `test/03_system/feature/usage/class_invariant_spec.spl` | style-difference | 223/225 | 347/350 | 2/4 |
| `test/03_system/net_connect_completion_spec.spl` | style-difference | 100/102 | 120/123 | 1/3 |
| `test/01_unit/app/doc_coverage/inline_comment_coverage_spec.spl` | style-difference | 275/276 | 339/341 | 9/10 |
| `test/01_unit/app/svllm_pack/main_spec.spl` | style-difference | 26/27 | 41/44 | 4/5 |
| `test/01_unit/compiler/blocks/builder_api_basic_spec.spl` | stale-use-only | 65/66 | 122/123 | 0/1 |
| `test/01_unit/compiler/blocks/builder_default_parser_spec.spl` | stale-use-only | 11/12 | 21/22 | 0/1 |
| `test/01_unit/compiler/blocks/easy_api_basic_spec.spl` | stale-use-only | 31/32 | 61/62 | 0/1 |
| `test/01_unit/compiler/blocks/testing_framework_spec.spl` | stale-use-only | 49/50 | 92/93 | 0/1 |
| `test/01_unit/compiler/blocks/utils_basic_spec.spl` | stale-use-only | 72/73 | 133/134 | 0/1 |
| `test/01_unit/compiler/frontend/required_comment_parse_spec.spl` | style-difference | 142/143 | 221/222 | 14/15 |
| `test/01_unit/compiler/mono/monomorphize_integration_spec.spl` | stale-use-only | 41/42 | 114/115 | 0/1 |
| `test/01_unit/compiler/parser/match_empty_array_bug_spec.spl` | stale-use-only | 71/72 | 189/190 | 0/1 |
| `test/01_unit/compiler/semantics/lint/required_comment_lint_spec.spl` | style-difference | 297/298 | 388/389 | 1/2 |
| `test/01_unit/gpu/graphics_3d_session_managed_backend_spec.spl` | style-difference | 307/308 | 386/387 | 2/3 |
| `test/01_unit/lib/common/collections_spec.spl` | style-difference | 213/214 | 298/299 | 1/2 |
| `test/01_unit/lib/common/mock_phase6_spec.spl` | style-difference | 872/873 | 1032/1033 | 1/2 |
| `test/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.spl` | style-difference | 22/23 | 27/27 | 1/2 |
| `test/01_unit/lib/crypto/ed25519_rfc8032_spec.spl` | style-difference | 157/158 | 249/250 | 2/3 |
| `test/01_unit/lib/driver/driver_manifest_test.spl` | style-difference | 122/123 | 148/150 | 2/3 |
| `test/02_integration/app/primitive_api_lint_spec.spl` | style-difference | 37/38 | 48/49 | 4/5 |
| `test/05_perf/ctype/bench_ctype_static_lut.spl` | style-difference | 116/117 | 134/136 | 4/5 |
| `test/05_perf/web_render_chrome/web_paint_cache_spec.spl` | style-difference | 104/105 | 155/156 | 18/20 |

## Worklist B — DISPROVEN (61): raw-ahead, NOT code-ahead — close unmerged

| numbered | class | code n/l | raw n/l | uniq num/leg |
|---|---|---|---|---|
| `test/01_unit/app/diagram/filter_spec.spl` | stub-legacy | 9/4 | 11/199 | 8/3 |
| `test/01_unit/app/doc/public_check/statistics_spec.spl` | stub-legacy | 15/4 | 19/241 | 13/3 |
| `test/01_unit/app/doc/public_check/warnings_spec.spl` | stub-legacy | 12/4 | 16/256 | 10/3 |
| `test/01_unit/app/formatter/formatter_basic_spec.spl` | stub-legacy | 12/4 | 16/170 | 11/3 |
| `test/01_unit/app/formatter/formatter_comprehensive_spec.spl` | stub-legacy | 13/4 | 17/1026 | 12/3 |
| `test/01_unit/app/formatter/formatter_spec.spl` | stub-legacy | 11/4 | 14/395 | 10/3 |
| `test/01_unit/app/formatter_spec.spl` | stub-legacy | 69/4 | 75/395 | 49/4 |
| `test/01_unit/app/io/cli_ops_handlers_spec.spl` | stub-legacy | 39/4 | 64/75 | 35/3 |
| `test/01_unit/app/package/ffi_spec.spl` | stub-legacy | 16/4 | 21/160 | 15/4 |
| `test/01_unit/app/package/package_spec.spl` | stub-legacy | 31/4 | 41/390 | 30/3 |
| `test/01_unit/app/tooling/color_utils_spec.spl` | stub-legacy | 14/4 | 18/232 | 13/3 |
| `test/01_unit/app/tooling/coverage_ffi_spec.spl` | stub-legacy | 14/4 | 18/288 | 12/3 |
| `test/01_unit/app/tooling/coverage_threshold_spec.spl` | stub-legacy | 24/4 | 30/97 | 22/3 |
| `test/01_unit/app/tooling/test_db_edge_cases_spec.spl` | stub-legacy | 19/4 | 25/317 | 17/3 |
| `test/01_unit/app/tooling/test_stats_spec.spl` | stub-legacy | 15/4 | 19/263 | 13/3 |
| `test/01_unit/baremetal/riscv/fpga_boot_linux_spec.spl` | style-difference | 122/122 | 200/201 | 4/4 |
| `test/01_unit/compiler/native/x86_64_simd_spec.spl` | stub-legacy | 217/4 | 255/349 | 158/4 |
| `test/01_unit/compiler_core/annotation_intrinsics_spec.spl` | stub-legacy | 29/4 | 38/93 | 28/3 |
| `test/01_unit/compiler_core/ast_clone_spec.spl` | stub-legacy | 37/4 | 43/145 | 32/3 |
| `test/01_unit/compiler_core/exhaustiveness_spec.spl` | stub-legacy | 35/4 | 41/120 | 31/3 |
| `test/01_unit/compiler_core/generic_syntax_spec.spl` | stub-legacy | 36/4 | 51/195 | 33/3 |
| `test/01_unit/compiler_core/ignored_return_warning_spec.spl` | stub-legacy | 30/4 | 37/147 | 27/3 |
| `test/01_unit/compiler_core/mir_spec.spl` | stub-legacy | 32/4 | 37/103 | 28/3 |
| `test/01_unit/compiler_core/mixin_expr_spec.spl` | stub-legacy | 28/4 | 35/136 | 26/3 |
| `test/01_unit/compiler_core/must_use_spec.spl` | style-difference | 34/4 | 40/157 | 31/3 |
| `test/01_unit/compiler_core/traits_compiles_spec.spl` | stub-legacy | 27/4 | 32/94 | 22/3 |
| `test/01_unit/compiler_core/traits_extended_spec.spl` | stub-legacy | 39/4 | 45/213 | 34/3 |
| `test/01_unit/compiler_core/traits_module_spec.spl` | stub-legacy | 22/4 | 27/152 | 18/3 |
| `test/01_unit/compiler_core/traits_spec.spl` | stub-legacy | 40/4 | 48/252 | 39/3 |
| `test/01_unit/compiler_shared/diagnostics/diagnostic_spec.spl` | stub-legacy | 19/4 | 24/254 | 17/3 |
| `test/01_unit/compiler_shared/diagnostics/label_spec.spl` | stub-legacy | 16/4 | 21/58 | 14/3 |
| `test/01_unit/compiler_shared/diagnostics/severity_spec.spl` | stub-legacy | 19/4 | 24/124 | 17/3 |
| `test/01_unit/compiler_shared/diagnostics/span_spec.spl` | stub-legacy | 18/4 | 23/116 | 16/3 |
| `test/01_unit/lib/common/color_utils_rgb_hsl_spec.spl` | stub-legacy | 20/4 | 26/467 | 19/3 |
| `test/01_unit/lib/common/compress/gzip_spec.spl` | style-difference | 173/172 | 204/205 | 1/0 |
| `test/01_unit/lib/common/context_spec.spl` | stub-legacy | 23/4 | 30/110 | 20/3 |
| `test/01_unit/lib/common/exp/artifact_spec.spl` | stub-legacy | 11/4 | 14/77 | 10/3 |
| `test/01_unit/lib/common/exp/config_spec.spl` | stub-legacy | 11/4 | 14/163 | 10/3 |
| `test/01_unit/lib/common/exp/storage_spec.spl` | stub-legacy | 11/4 | 14/90 | 10/3 |
| `test/01_unit/lib/common/exp/sweep_spec.spl` | stub-legacy | 14/4 | 17/150 | 13/3 |
| `test/01_unit/lib/common/hooks/hook_registry_spec.spl` | stub-legacy | 29/4 | 39/181 | 26/3 |
| `test/01_unit/lib/common/mock_phase4_spec.spl` | style-difference | 502/502 | 609/610 | 9/9 |
| `test/01_unit/lib/common/newline_constants_spec.spl` | stub-legacy | 16/4 | 21/116 | 14/3 |
| `test/01_unit/lib/common/pure/data_loader_spec.spl` | stub-legacy | 16/4 | 21/111 | 14/3 |
| `test/01_unit/lib/common/string_core_spec.spl` | stub-legacy | 16/4 | 21/186 | 14/3 |
| `test/01_unit/lib/nogc_async_mut/async_embedded_spec.spl` | genuine-merge | 4/4 | 4/248 | 0/0 |
| `test/01_unit/lib/nogc_async_mut/async_host_spec.spl` | stub-legacy | 66/4 | 74/380 | 65/3 |
| `test/01_unit/lib/qemu_spec.spl` | stub-legacy | 44/4 | 50/222 | 39/3 |
| `test/01_unit/std/context_spec.spl` | stub-legacy | 15/4 | 20/110 | 14/3 |
| `test/01_unit/std/exp/artifact_spec.spl` | stub-legacy | 11/4 | 14/77 | 10/3 |
| `test/01_unit/std/exp/config_spec.spl` | stub-legacy | 11/4 | 14/163 | 10/3 |
| `test/01_unit/std/exp/run_spec.spl` | stub-legacy | 12/4 | 15/111 | 11/3 |
| `test/01_unit/std/exp/sweep_spec.spl` | stub-legacy | 14/4 | 17/150 | 13/3 |
| `test/01_unit/std/hooks/hook_registry_spec.spl` | stub-legacy | 19/4 | 26/181 | 16/3 |
| `test/02_integration/app/linkers_log_modes_spec.spl` | style-difference | 35/35 | 41/42 | 2/2 |
| `test/02_integration/os/port/bootstrap_cross_status_spec.spl` | style-difference | 14/14 | 22/23 | 2/2 |
| `test/03_system/app/compiler/feature/all_regions_spec.spl` | stale-use-only | 17/17 | 20/21 | 1/1 |
| `test/03_system/database/server/db_durability_spec.spl` | style-difference | 359/359 | 453/469 | 1/1 |
| `test/03_system/feature/usage/alias_deprecated_spec.spl` | style-difference | 320/306 | 594/596 | 27/4 |
| `test/03_system/feature/usage/static_const_declarations_spec.spl` | style-difference | 344/344 | 540/576 | 1/4 |
| `test/05_perf/ctype/global_static_array_smoke.spl` | style-difference | 21/21 | 25/26 | 2/2 |

## Worklist C — equal raw length, different content (355)

| numbered | class | code n/l | raw n/l | uniq num/leg |
|---|---|---|---|---|
| `test/01_unit/app/branch_coverage_7_spec.spl` | style-difference | 346/346 | 442/442 | 3/3 |
| `test/01_unit/app/cli/cli_migration_spec.spl` | style-difference | 17/17 | 27/27 | 1/1 |
| `test/01_unit/app/cli/cli_os_spec.spl` | style-difference | 22/22 | 29/29 | 9/9 |
| `test/01_unit/app/cli/query_visibility_spec.spl` | style-difference | 18/18 | 24/24 | 1/1 |
| `test/01_unit/app/cli_help_alignment_spec.spl` | style-difference | 193/193 | 262/262 | 1/1 |
| `test/01_unit/app/cmm_lsp/cmm_dialog_label_ref_spec.spl` | style-difference | 257/257 | 296/296 | 1/1 |
| `test/01_unit/app/dap/debug_adapter_spec.spl` | style-difference | 156/156 | 253/253 | 43/43 |
| `test/01_unit/app/dap/debug_configuration_spec.spl` | style-difference | 119/119 | 196/196 | 32/32 |
| `test/01_unit/app/dap/debug_session_spec.spl` | style-difference | 140/140 | 225/225 | 27/27 |
| `test/01_unit/app/dap/debug_state_spec.spl` | style-difference | 85/85 | 138/138 | 24/24 |
| `test/01_unit/app/doc_coverage/group_comment_detection_spec.spl` | style-difference | 305/305 | 369/369 | 8/8 |
| `test/01_unit/app/doc_coverage/tag_validator_spec.spl` | stale-use-only | 244/244 | 360/360 | 1/1 |
| `test/01_unit/app/doc_coverage/threshold_calculator_spec.spl` | stale-use-only | 240/240 | 391/391 | 2/2 |
| `test/01_unit/app/fix/lint_spec.spl` | stale-use-only | 22/22 | 36/36 | 2/2 |
| `test/01_unit/app/inventory_drift_spec.spl` | style-difference | 357/357 | 426/426 | 1/1 |
| `test/01_unit/app/llm_caret/gemini_cli_spec.spl` | style-difference | 316/318 | 406/406 | 2/4 |
| `test/01_unit/app/lsp/code_action_kind_spec.spl` | style-difference | 130/130 | 204/204 | 27/27 |
| `test/01_unit/app/lsp/helper_functions_spec.spl` | style-difference | 99/99 | 153/153 | 17/17 |
| `test/01_unit/app/lsp/server_capabilities_spec.spl` | style-difference | 151/151 | 239/239 | 32/32 |
| `test/01_unit/app/lsp/symbol_kind_spec.spl` | style-difference | 276/276 | 448/448 | 65/65 |
| `test/01_unit/app/lsp/workspace_edit_spec.spl` | style-difference | 153/153 | 237/237 | 34/34 |
| `test/01_unit/app/mcp_t32/mcp_t32_wsl_wrapper_spec.spl` | style-difference | 229/229 | 334/334 | 1/1 |
| `test/01_unit/app/mcp_unit/assistant_task_linking_spec.spl` | style-difference | 34/34 | 42/42 | 1/1 |
| `test/01_unit/app/mcp_unit/coordinator_extended_spec.spl` | style-difference | 293/293 | 353/353 | 2/2 |
| `test/01_unit/app/mcp_unit/crash_prevention_spec.spl` | style-difference | 160/160 | 205/205 | 4/1 |
| `test/01_unit/app/mcp_unit/debug_coordinator_spec.spl` | style-difference | 240/240 | 297/297 | 7/3 |
| `test/01_unit/app/mcp_unit/editor_spec.spl` | genuine-merge | 4/4 | 146/146 | 0/0 |
| `test/01_unit/app/mcp_unit/error_handler_edge_cases_spec.spl` | style-difference | 98/98 | 123/123 | 1/1 |
| `test/01_unit/app/mcp_unit/fileio_protection_spec.spl` | style-difference | 208/208 | 268/268 | 19/19 |
| `test/01_unit/app/mcp_unit/mcp_inventory_alignment_spec.spl` | style-difference | 399/399 | 476/476 | 13/13 |
| `test/01_unit/app/mcp_unit/server_safe_operations_spec.spl` | style-difference | 66/66 | 83/83 | 2/1 |
| `test/01_unit/app/mcp_unit/tasks_spec.spl` | style-difference | 520/520 | 642/642 | 70/68 |
| `test/01_unit/app/mcp_unit/transport_error_handling_spec.spl` | style-difference | 104/104 | 139/139 | 2/1 |
| `test/01_unit/app/mcp_unit/transport_tcp_spec.spl` | style-difference | 103/103 | 136/136 | 1/1 |
| `test/01_unit/app/mcp_unit/validation_spec.spl` | style-difference | 142/142 | 177/177 | 8/1 |
| `test/01_unit/app/simpleos_nvme_serial_check_spec.spl` | style-difference | 1399/1399 | 1547/1547 | 14/15 |
| `test/01_unit/app/test_daemon/test_daemon_gui_routing_spec.spl` | style-difference | 58/58 | 88/88 | 1/1 |
| `test/01_unit/app/test_runner/types_spec.spl` | style-difference | 324/324 | 406/406 | 6/6 |
| `test/01_unit/app/test_runner_new/container_backend_spec.spl` | style-difference | 74/74 | 91/91 | 2/1 |
| `test/01_unit/app/tooling/arg_parsing_spec.spl` | style-difference | 137/137 | 179/179 | 1/1 |
| `test/01_unit/app/tooling/compile_commands_spec.spl` | style-difference | 182/182 | 251/251 | 3/3 |
| `test/01_unit/app/tooling/todo_parser_spec.spl` | genuine-merge | 119/119 | 231/231 | 0/0 |
| `test/01_unit/app/tooling/tooling_spec.spl` | style-difference | 67/67 | 270/270 | 1/1 |
| `test/01_unit/app/ui.chromium/js_audit_spec.spl` | genuine-merge | 166/166 | 240/240 | 0/0 |
| `test/01_unit/app/ui.chromium/text_metrics_spec.spl` | style-difference | 164/164 | 201/201 | 2/2 |
| `test/01_unit/app/ui.electron/main_spec.spl` | style-difference | 34/34 | 56/56 | 1/1 |
| `test/01_unit/app/ui/cli_observer_spec.spl` | stale-use-only | 105/105 | 146/146 | 1/1 |
| `test/01_unit/app/ui/cli_socket_spec.spl` | stale-use-only | 74/74 | 108/108 | 1/1 |
| `test/01_unit/app/ui/ipc_surface_spec.spl` | stale-use-only | 51/51 | 77/77 | 1/1 |
| `test/01_unit/app/ui/tauri_entry_common_envelope_spec.spl` | style-difference | 15/15 | 16/16 | 2/2 |
| `test/01_unit/app/ui/widget_button_checkbox_dropdown_spec.spl` | style-difference | 333/333 | 441/441 | 7/6 |
| `test/01_unit/app/ui/widget_menu_tooltip_spec.spl` | style-difference | 197/197 | 281/281 | 2/2 |
| `test/01_unit/app/ui/widget_menubar_statusbar_spec.spl` | stale-use-only | 379/379 | 500/500 | 1/1 |
| `test/01_unit/app/ui/widget_modifiers_spec.spl` | stale-use-only | 153/153 | 198/198 | 1/1 |
| `test/01_unit/app/ui/widget_panel_text_divider_spec.spl` | stale-use-only | 456/456 | 552/552 | 1/1 |
| `test/01_unit/app/ui/widget_progress_image_tooltip_spec.spl` | stale-use-only | 352/352 | 462/462 | 1/1 |
| `test/01_unit/app/ui/widget_scroll_textarea_spec.spl` | stale-use-only | 211/211 | 279/279 | 1/1 |
| `test/01_unit/app/ui/widget_tabs_list_dialog_spec.spl` | stale-use-only | 384/384 | 489/489 | 1/1 |
| `test/01_unit/app/ui/widget_tree_spec.spl` | stale-use-only | 192/192 | 267/267 | 1/1 |
| `test/01_unit/compiler/60.mir_opt/general_patterns_spec.spl` | style-difference | 304/304 | 365/365 | 5/1 |
| `test/01_unit/compiler/async/async_mir_interpreter_spec.spl` | style-difference | 25/25 | 40/40 | 7/1 |
| `test/01_unit/compiler/async/async_state_machine_spec.spl` | genuine-merge | 4/4 | 273/273 | 0/0 |
| `test/01_unit/compiler/async/poll_generator_spec.spl` | genuine-merge | 4/4 | 243/243 | 0/0 |
| `test/01_unit/compiler/backend/spipe_system_test_spec.spl` | genuine-merge | 105/105 | 159/159 | 0/0 |
| `test/01_unit/compiler/backend/vhdl_testbench_spec.spl` | style-difference | 240/240 | 255/255 | 1/1 |
| `test/01_unit/compiler/codegen/baremetal_cross_module_val_spec.spl` | genuine-merge | 10/10 | 92/92 | 0/0 |
| `test/01_unit/compiler/codegen/baremetal_method_dispatch_spec.spl` | genuine-merge | 30/30 | 80/80 | 0/0 |
| `test/01_unit/compiler/codegen/method_dispatch_uncovered_gaps_spec.spl` | style-difference | 53/53 | 112/112 | 13/1 |
| `test/01_unit/compiler/coverage/branch_coverage_10_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_11_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_12_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_14_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_15_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_16_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_18_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_19_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_1_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_20_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_21_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_22_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_23_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_24_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_25_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_2_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_3_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_4_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_5_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_6_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_7_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_8_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/coverage/branch_coverage_9_spec.spl` | style-difference | 346/346 | 442/442 | 4/4 |
| `test/01_unit/compiler/driver/main_opt_level_cli_spec.spl` | style-difference | 28/28 | 34/34 | 1/1 |
| `test/01_unit/compiler/hir/hir_stage4_field_inference_spec.spl` | style-difference | 107/107 | 139/139 | 1/1 |
| `test/01_unit/compiler/interpreter/mir_ssa_phi_intrinsic_spec.spl` | style-difference | 58/58 | 64/64 | 1/1 |
| `test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl` | style-difference | 154/154 | 173/173 | 16/16 |
| `test/01_unit/compiler/loader/metadata_symbols_spec.spl` | stale-use-only | 78/78 | 87/87 | 1/1 |
| `test/01_unit/compiler/mir/mir_pattern_idiom_benchmark_spec.spl` | style-difference | 188/188 | 251/251 | 10/4 |
| `test/01_unit/compiler/mir/synthetic_driver_registration_spec.spl` | style-difference | 187/187 | 221/221 | 2/2 |
| `test/01_unit/compiler/mir_opt/constant_folding_spec.spl` | style-difference | 82/82 | 93/93 | 2/1 |
| `test/01_unit/compiler/mir_opt/strength_reduction_spec.spl` | style-difference | 156/156 | 180/180 | 1/1 |
| `test/01_unit/compiler/module_resolver/type_domain_resolver_spec.spl` | style-difference | 50/50 | 56/56 | 2/1 |
| `test/01_unit/compiler/parser/bitfield_pure_simple_spec.spl` | style-difference | 21/21 | 27/27 | 1/1 |
| `test/01_unit/compiler/parser/paren_call_block_spec.spl` | style-difference | 13/13 | 28/28 | 1/1 |
| `test/01_unit/compiler/parser/treesitter_highlights_spec.spl` | style-difference | 29/29 | 45/45 | 1/1 |
| `test/01_unit/compiler/parser/treesitter_visibility_spec.spl` | style-difference | 25/25 | 35/35 | 2/2 |
| `test/01_unit/compiler/r2_lang_probe_spec.spl` | stale-use-only | 6/6 | 8/8 | 1/1 |
| `test/01_unit/compiler/semantics/uncovered_branches_spec.spl` | style-difference | 180/180 | 284/284 | 4/4 |
| `test/01_unit/compiler/tools/duplicate_check_debug_spec.spl` | style-difference | 33/33 | 58/58 | 1/1 |
| `test/01_unit/compiler/types/layout_verification_spec.spl` | style-difference | 335/335 | 457/457 | 12/12 |
| `test/01_unit/compiler/types/runtime_layout_verification_spec.spl` | style-difference | 188/188 | 249/249 | 4/4 |
| `test/01_unit/compiler_core/branch_coverage_12_spec.spl` | style-difference | 346/346 | 442/442 | 3/3 |
| `test/01_unit/compiler_core/branch_coverage_23_spec.spl` | style-difference | 346/346 | 442/442 | 3/3 |
| `test/01_unit/doc/feature_requests_spec.spl` | style-difference | 16/16 | 24/24 | 1/1 |
| `test/01_unit/fs_driver/error_test.spl` | style-difference | 83/83 | 125/125 | 10/10 |
| `test/01_unit/fs_driver/extension_test.spl` | style-difference | 208/208 | 266/266 | 4/4 |
| `test/01_unit/fs_driver/instance_test.spl` | style-difference | 56/56 | 87/87 | 2/1 |
| `test/01_unit/hardware/fpga_linux/check_riscv_rtl_linux_smoke_spec.spl` | style-difference | 10/10 | 12/12 | 1/1 |
| `test/01_unit/jit/jit_riscv_hotspot_opt_spec.spl` | style-difference | 72/72 | 101/101 | 2/1 |
| `test/01_unit/lib/branch_coverage_24_spec.spl` | style-difference | 346/346 | 442/442 | 3/3 |
| `test/01_unit/lib/branch_coverage_3_spec.spl` | style-difference | 346/346 | 442/442 | 3/3 |
| `test/01_unit/lib/cc/property_tree_spec.spl` | style-difference | 69/69 | 81/81 | 1/1 |
| `test/01_unit/lib/common/auto_comprehensive_10_spec.spl` | style-difference | 154/154 | 191/191 | 1/1 |
| `test/01_unit/lib/common/auto_comprehensive_24_spec.spl` | style-difference | 154/154 | 191/191 | 1/1 |
| `test/01_unit/lib/common/compatibility_spec.spl` | genuine-merge | 30/30 | 54/54 | 0/0 |
| `test/01_unit/lib/common/compress_facade_harness_spec.spl` | style-difference | 150/150 | 169/169 | 1/1 |
| `test/01_unit/lib/common/compress_framework_spec.spl` | style-difference | 352/352 | 385/385 | 11/4 |
| `test/01_unit/lib/common/compress_utilities_spec.spl` | style-difference | 120/120 | 136/136 | 2/2 |
| `test/01_unit/lib/common/contracts/new_contracts_spec.spl` | style-difference | 28/28 | 41/41 | 7/1 |
| `test/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.spl` | style-difference | 22/23 | 27/27 | 1/2 |
| `test/01_unit/lib/common/crypto/sha1_spec.spl` | genuine-merge | 62/62 | 125/125 | 0/0 |
| `test/01_unit/lib/common/ds_utils_stack_queue_spec.spl` | style-difference | 316/316 | 403/403 | 17/17 |
| `test/01_unit/lib/common/export_star_spec.spl` | style-difference | 53/53 | 69/69 | 2/2 |
| `test/01_unit/lib/common/hpack/huffman_h2_spec.spl` | style-difference | 166/166 | 259/259 | 2/2 |
| `test/01_unit/lib/common/hpack/string_codec_spec.spl` | style-difference | 105/105 | 146/146 | 2/2 |
| `test/01_unit/lib/common/js_jit_optimizer_spec.spl` | style-difference | 119/119 | 138/138 | 2/2 |
| `test/01_unit/lib/common/js_runtime_node_fast_path_spec.spl` | style-difference | 48/48 | 57/57 | 1/1 |
| `test/01_unit/lib/common/let_memoization_spec.spl` | stale-use-only | 69/69 | 122/122 | 1/1 |
| `test/01_unit/lib/common/log_export_spec.spl` | style-difference | 23/23 | 45/45 | 6/6 |
| `test/01_unit/lib/common/math_repr_plain_coverage_spec.spl` | style-difference | 562/562 | 791/791 | 1/1 |
| `test/01_unit/lib/common/option_spec.spl` | stale-use-only | 69/69 | 94/94 | 1/1 |
| `test/01_unit/lib/common/parser_spec.spl` | genuine-merge | 40/40 | 70/70 | 0/0 |
| `test/01_unit/lib/common/pending_on_spec.spl` | style-difference | 22/22 | 57/57 | 1/1 |
| `test/01_unit/lib/common/perf_optimization_spec.spl` | style-difference | 389/389 | 565/565 | 23/23 |
| `test/01_unit/lib/common/png_decode_spec.spl` | style-difference | 42/42 | 95/95 | 1/1 |
| `test/01_unit/lib/common/regex_char_utils_coverage_spec.spl` | stale-use-only | 883/883 | 1421/1421 | 1/1 |
| `test/01_unit/lib/common/roundtrip_spec.spl` | stale-use-only | 123/123 | 145/145 | 2/2 |
| `test/01_unit/lib/common/sdn_coverage_spec.spl` | stale-use-only | 312/312 | 437/437 | 4/4 |
| `test/01_unit/lib/common/spec_framework_spec.spl` | style-difference | 38/38 | 69/69 | 2/1 |
| `test/01_unit/lib/common/test_meta_spec.spl` | style-difference | 53/53 | 239/239 | 12/12 |
| `test/01_unit/lib/common/value_spec.spl` | genuine-merge | 54/54 | 83/83 | 0/0 |
| `test/01_unit/lib/common/web/browser_session_node_host_gc_async_spec.spl` | style-difference | 35/35 | 41/41 | 1/1 |
| `test/01_unit/lib/common/web/simple_browser_page_spec.spl` | style-difference | 86/86 | 98/98 | 9/1 |
| `test/01_unit/lib/common/win_fs/window_record_spec.spl` | style-difference | 37/37 | 45/45 | 1/1 |
| `test/01_unit/lib/common/window_protocol/input_translator_spec.spl` | genuine-merge | 64/64 | 76/76 | 0/0 |
| `test/01_unit/lib/common/xz_lzma2_periodic_encode_spec.spl` | style-difference | 120/120 | 138/138 | 3/3 |
| `test/01_unit/lib/common/zstd_frame_variants_spec.spl` | style-difference | 358/358 | 395/395 | 1/1 |
| `test/01_unit/lib/common/zstd_sequence_rle_spec.spl` | style-difference | 124/124 | 134/134 | 1/1 |
| `test/01_unit/lib/crypto/aes256_gcm_nist_vectors_spec.spl` | style-difference | 209/209 | 294/294 | 2/2 |
| `test/01_unit/lib/crypto/aes256_simd_round_spec.spl` | genuine-merge | 147/147 | 211/211 | 0/0 |
| `test/01_unit/lib/crypto/aes_ctr_nist_spec.spl` | style-difference | 53/53 | 103/103 | 5/5 |
| `test/01_unit/lib/crypto/aes_gcm_siv_rfc8452_kat_spec.spl` | style-difference | 145/145 | 253/253 | 6/2 |
| `test/01_unit/lib/crypto/p256_ct_property_spec.spl` | genuine-merge | 87/87 | 149/149 | 0/0 |
| `test/01_unit/lib/crypto/rsa_pss_sha256_kat_spec.spl` | genuine-merge | 116/116 | 193/193 | 0/0 |
| `test/01_unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl` | genuine-merge | 100/100 | 137/137 | 0/0 |
| `test/01_unit/lib/crypto/sha1_x4_spec.spl` | stale-use-only | 126/126 | 187/187 | 1/1 |
| `test/01_unit/lib/database/sql/sql_interceptor_spec.spl` | style-difference | 148/148 | 176/176 | 6/6 |
| `test/01_unit/lib/database/sql/sql_repository_spec.spl` | genuine-merge | 185/185 | 221/221 | 0/1 |
| `test/01_unit/lib/database/sql/sql_types_spec.spl` | style-difference | 253/253 | 324/324 | 3/2 |
| `test/01_unit/lib/debug/remote/session_model_spec.spl` | style-difference | 41/41 | 45/45 | 3/1 |
| `test/01_unit/lib/dependency_boundary_spec.spl` | style-difference | 166/166 | 212/212 | 1/1 |
| `test/01_unit/lib/editor/editor_launch_contract_spec.spl` | style-difference | 49/49 | 63/63 | 4/4 |
| `test/01_unit/lib/editor/host_simpleos_surface_contract_spec.spl` | style-difference | 103/103 | 120/120 | 4/4 |
| `test/01_unit/lib/editor/unified/unified_backend_spec.spl` | style-difference | 137/137 | 173/173 | 2/2 |
| `test/01_unit/lib/engine/physics/physics2/raycast_spec.spl` | style-difference | 51/51 | 58/58 | 3/3 |
| `test/01_unit/lib/engine/physics/physics2/world2d_spec.spl` | style-difference | 94/94 | 107/107 | 2/2 |
| `test/01_unit/lib/engine/physics/physics2/world3d_spec.spl` | style-difference | 61/61 | 69/69 | 2/2 |
| `test/01_unit/lib/engine/vector_spec.spl` | style-difference | 53/53 | 63/63 | 3/3 |
| `test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl` | style-difference | 359/359 | 405/405 | 4/4 |
| `test/01_unit/lib/gc_async_immut/facade_resolution_spec.spl` | style-difference | 12/12 | 17/17 | 1/1 |
| `test/01_unit/lib/gc_async_immut/native_combinators_spec.spl` | style-difference | 5/5 | 8/8 | 1/1 |
| `test/01_unit/lib/gc_async_mut/database/vector/database_vector_facade_spec.spl` | style-difference | 42/42 | 47/47 | 2/2 |
| `test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl` | style-difference | 38/38 | 42/42 | 4/4 |
| `test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_engine_facade_spec.spl` | style-difference | 32/32 | 35/35 | 1/1 |
| `test/01_unit/lib/gc_async_mut/engine/llm/engine_llm_facade_spec.spl` | style-difference | 44/44 | 51/51 | 1/1 |
| `test/01_unit/lib/gc_async_mut/mcp_sdk/core/core_facade_spec.spl` | style-difference | 17/17 | 22/22 | 1/1 |
| `test/01_unit/lib/gc_async_mut/src/tooling/tooling_facade_spec.spl` | style-difference | 22/22 | 25/25 | 1/1 |
| `test/01_unit/lib/gc_async_mut/text_layout/text_layout_facade_spec.spl` | style-difference | 22/22 | 27/27 | 2/2 |
| `test/01_unit/lib/gc_sync_immut/facade_resolution_spec.spl` | style-difference | 12/12 | 17/17 | 1/1 |
| `test/01_unit/lib/gc_sync_immut/native_combinators_spec.spl` | style-difference | 5/5 | 8/8 | 1/1 |
| `test/01_unit/lib/http/h3/h3_frame_round_trip_spec.spl` | style-difference | 235/235 | 327/327 | 4/1 |
| `test/01_unit/lib/nogc_async_mut/async_host_mt_spec.spl` | genuine-merge | 4/4 | 308/308 | 0/0 |
| `test/01_unit/lib/nogc_async_mut/concurrent_providers_spec.spl` | style-difference | 565/565 | 709/709 | 6/6 |
| `test/01_unit/lib/nogc_async_mut/concurrent_wrappers_spec.spl` | style-difference | 322/322 | 437/437 | 4/4 |
| `test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl` | style-difference | 38/38 | 42/42 | 4/4 |
| `test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_engine_facade_spec.spl` | style-difference | 32/32 | 35/35 | 1/1 |
| `test/01_unit/lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.spl` | style-difference | 44/44 | 51/51 | 1/1 |
| `test/01_unit/lib/nogc_async_mut/host_future_intensive_spec.spl` | style-difference | 334/334 | 477/477 | 1/1 |
| `test/01_unit/lib/nogc_async_mut/http/http_hardening_spec.spl` | style-difference | 243/243 | 282/282 | 4/3 |
| `test/01_unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.spl` | style-difference | 103/103 | 157/157 | 4/4 |
| `test/01_unit/lib/nogc_async_mut/mcp_sdk/core/core_facade_spec.spl` | style-difference | 17/17 | 22/22 | 1/1 |
| `test/01_unit/lib/nogc_async_mut/promise_intensive_spec.spl` | style-difference | 406/406 | 493/493 | 1/1 |
| `test/01_unit/lib/nogc_async_mut/src/tooling/tooling_facade_spec.spl` | style-difference | 22/22 | 25/25 | 1/1 |
| `test/01_unit/lib/nogc_async_mut/text_layout/text_layout_facade_spec.spl` | style-difference | 22/22 | 27/27 | 2/2 |
| `test/01_unit/lib/nogc_async_mut/tls/ech_spec.spl` | style-difference | 45/45 | 54/54 | 4/2 |
| `test/01_unit/lib/nogc_sync_mut/compression/zstd/fse_spec.spl` | style-difference | 209/209 | 293/293 | 1/1 |
| `test/01_unit/lib/nogc_sync_mut/compression/zstd/zstd_spec.spl` | style-difference | 344/344 | 470/470 | 1/1 |
| `test/01_unit/lib/nogc_sync_mut/engine/render/backend3d_spec.spl` | style-difference | 162/162 | 209/209 | 1/1 |
| `test/01_unit/lib/nogc_sync_mut/engine/render/gpu_lighting3d_spec.spl` | style-difference | 146/146 | 182/182 | 8/4 |
| `test/01_unit/lib/play/session_store_spec.spl` | style-difference | 89/89 | 125/125 | 4/2 |
| `test/01_unit/lib/security/security_support_spec.spl` | style-difference | 262/262 | 285/285 | 5/1 |
| `test/01_unit/lib/std/file/file_io_spec.spl` | style-difference | 22/22 | 31/31 | 3/3 |
| `test/01_unit/lib/std/ml/tracking/run_spec.spl` | style-difference | 38/38 | 70/70 | 2/1 |
| `test/01_unit/lib/std/time_spec.spl` | style-difference | 123/123 | 163/163 | 4/4 |
| `test/01_unit/lib/text/utf8_validation_spec.spl` | stale-use-only | 113/113 | 146/146 | 1/1 |
| `test/01_unit/lib/viz/damage_spec.spl` | style-difference | 117/117 | 156/156 | 2/2 |
| `test/01_unit/os/apps/sshd/ssh_packet_spec.spl` | style-difference | 125/125 | 146/146 | 1/1 |
| `test/01_unit/os/compositor/gpu_glass_spec.spl` | style-difference | 49/49 | 87/87 | 1/1 |
| `test/01_unit/os/compositor/layout_manager_spec.spl` | style-difference | 296/296 | 409/409 | 2/2 |
| `test/01_unit/os/compositor/qemu_capture_ppm_spec.spl` | style-difference | 131/131 | 197/197 | 2/2 |
| `test/01_unit/os/crypto/chacha20_simd_parity_spec.spl` | genuine-merge | 101/101 | 146/146 | 0/0 |
| `test/01_unit/os/crypto/sm3_kat_spec.spl` | genuine-merge | 157/168 | 190/190 | 0/6 |
| `test/01_unit/os/desktop/desktop_e2e_shortcut_flow_spec.spl` | style-difference | 14/14 | 19/19 | 1/1 |
| `test/01_unit/os/desktop/dock_spec.spl` | style-difference | 415/415 | 522/522 | 14/14 |
| `test/01_unit/os/drivers/nvme/nvme_physical_preflight_script_spec.spl` | style-difference | 220/220 | 248/248 | 2/2 |
| `test/01_unit/os/drivers/nvme/nvme_storage_model_spec.spl` | style-difference | 755/755 | 794/794 | 1/1 |
| `test/01_unit/os/drivers/real_device_readiness_spec.spl` | style-difference | 547/547 | 568/568 | 2/2 |
| `test/01_unit/os/kernel/arch/gdt_layout_spec.spl` | style-difference | 46/46 | 80/80 | 9/9 |
| `test/01_unit/os/kernel/arch/syscall_dispatch_spec.spl` | style-difference | 147/147 | 176/176 | 59/59 |
| `test/01_unit/os/kernel/arch/syscall_entry_spec.spl` | genuine-merge | 39/39 | 71/71 | 0/0 |
| `test/01_unit/os/kernel/ipc/ipc_error_codes_spec.spl` | style-difference | 47/47 | 65/65 | 1/1 |
| `test/01_unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.spl` | style-difference | 55/55 | 80/80 | 1/1 |
| `test/01_unit/os/kernel/ipc/ipc_port_create_hosted_spec.spl` | style-difference | 78/78 | 88/88 | 1/1 |
| `test/01_unit/os/kernel/loader/spawn_pipeline_spec.spl` | style-difference | 306/306 | 395/395 | 1/1 |
| `test/01_unit/os/kernel/loader/zstd_decompress_spec.spl` | style-difference | 17/17 | 20/20 | 2/2 |
| `test/01_unit/os/memory/mold_linker_spec.spl` | style-difference | 92/92 | 140/140 | 4/4 |
| `test/01_unit/os/multiarch/hardening_gates_spec.spl` | style-difference | 177/177 | 236/236 | 4/4 |
| `test/01_unit/os/process_isolation_as_spec.spl` | style-difference | 122/124 | 166/166 | 3/4 |
| `test/01_unit/os/qemu_runner_desktop_extended_spec.spl` | style-difference | 246/246 | 265/265 | 7/7 |
| `test/01_unit/os/qemu_runner_raw_image_validator_spec.spl` | style-difference | 193/193 | 207/207 | 7/7 |
| `test/01_unit/os/services/vfs/nvme_filesystem_mounts_spec.spl` | style-difference | 280/280 | 307/307 | 3/1 |
| `test/01_unit/os/simpleos_board_hardening_spec.spl` | style-difference | 247/247 | 272/272 | 4/4 |
| `test/01_unit/os/tls12/tls12_record_handshake_round_trip_spec.spl` | style-difference | 250/250 | 346/346 | 1/1 |
| `test/01_unit/os/tls13/aes256_gcm_sha384_cipher_suite_spec.spl` | style-difference | 145/145 | 217/217 | 3/2 |
| `test/01_unit/os/tls13/chacha20_poly1305_cipher_suite_spec.spl` | style-difference | 213/213 | 310/310 | 6/2 |
| `test/01_unit/os/tls13/encrypted_extensions_spec.spl` | style-difference | 139/139 | 210/210 | 1/1 |
| `test/01_unit/os/tls13/hello_retry_request_spec.spl` | style-difference | 285/285 | 399/399 | 1/1 |
| `test/01_unit/os/tls13/key_update_spec.spl` | style-difference | 139/139 | 207/207 | 8/2 |
| `test/01_unit/runtime/process_is_running_spec.spl` | style-difference | 44/46 | 72/72 | 19/24 |
| `test/01_unit/sffi/sffi_public_api_spec.spl` | style-difference | 114/112 | 207/207 | 4/2 |
| `test/01_unit/std/auto_comprehensive_13_spec.spl` | style-difference | 165/165 | 202/202 | 1/1 |
| `test/01_unit/std/auto_comprehensive_17_spec.spl` | style-difference | 165/165 | 202/202 | 1/1 |
| `test/01_unit/std/auto_comprehensive_24_spec.spl` | style-difference | 165/165 | 202/202 | 1/1 |
| `test/01_unit/std/mock_direct_spec.spl` | style-difference | 24/24 | 33/33 | 3/3 |
| `test/01_unit/std/mock_recorder_spec.spl` | style-difference | 24/24 | 33/33 | 3/3 |
| `test/01_unit/std/mock_simple_spec.spl` | style-difference | 14/14 | 17/17 | 1/1 |
| `test/01_unit/std/module_import_spec.spl` | style-difference | 71/71 | 130/130 | 21/1 |
| `test/01_unit/std/parser_spec.spl` | genuine-merge | 40/40 | 70/70 | 0/0 |
| `test/01_unit/std/perf_optimization_spec.spl` | style-difference | 395/395 | 565/565 | 24/24 |
| `test/01_unit/std/test_meta_spec.spl` | style-difference | 53/53 | 240/240 | 12/12 |
| `test/01_unit/test_runner/mode_filter_spec.spl` | style-difference | 124/124 | 147/147 | 5/5 |
| `test/01_unit/tools/cat_spec.spl` | style-difference | 24/24 | 32/32 | 1/1 |
| `test/02_integration/app/app_mcp_intensive_spec.spl` | style-difference | 390/390 | 522/522 | 35/36 |
| `test/02_integration/app/feature_gen_log_modes_spec.spl` | style-difference | 38/38 | 46/46 | 3/3 |
| `test/02_integration/app/io_runtime_import_spec.spl` | style-difference | 39/39 | 49/49 | 1/1 |
| `test/02_integration/app/spec_coverage_log_modes_spec.spl` | style-difference | 43/43 | 52/52 | 2/2 |
| `test/02_integration/app/ui.web/reconnect_test.spl` | stale-use-only | 122/122 | 194/194 | 1/1 |
| `test/02_integration/app/ui/main_render_spec.spl` | style-difference | 243/243 | 347/347 | 3/3 |
| `test/02_integration/app/ui_browser_log_modes_spec.spl` | style-difference | 58/58 | 67/67 | 2/2 |
| `test/02_integration/app/web_stack_sample_persistence_spec.spl` | style-difference | 15/15 | 18/18 | 4/4 |
| `test/02_integration/app/web_stack_sample_spec.spl` | style-difference | 57/57 | 63/63 | 2/2 |
| `test/02_integration/baremetal/remote_riscv32_spec.spl` | style-difference | 644/644 | 909/909 | 13/13 |
| `test/02_integration/compiler/import_syntax_spec.spl` | style-difference | 20/20 | 35/35 | 1/1 |
| `test/02_integration/compiler/llvm_compiled_proof_spec.spl` | style-difference | 349/349 | 481/481 | 1/1 |
| `test/02_integration/compiler/llvm_parity_spec.spl` | style-difference | 89/89 | 114/114 | 5/5 |
| `test/02_integration/compiler/vhdl_backend_e2e_spec.spl` | style-difference | 1558/1558 | 1818/1818 | 12/12 |
| `test/02_integration/ffi_gen/math_migration_test.spl` | style-difference | 132/132 | 183/183 | 1/1 |
| `test/02_integration/fs_driver/capability_dispatch_test.spl` | style-difference | 120/120 | 186/186 | 11/10 |
| `test/02_integration/fs_driver/multi_mount_test.spl` | style-difference | 167/167 | 257/257 | 12/12 |
| `test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl` | style-difference | 203/203 | 277/277 | 1/1 |
| `test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl` | style-difference | 310/310 | 416/416 | 1/0 |
| `test/02_integration/os/port/rust/smoke_rustc_spec.spl` | style-difference | 73/73 | 100/100 | 2/2 |
| `test/02_integration/remote_jit/arduino_r4_composite_runner_spec.spl` | genuine-merge | 90/90 | 106/106 | 0/1 |
| `test/02_integration/remote_jit/esp32_composite_runner_spec.spl` | genuine-merge | 87/87 | 103/103 | 0/1 |
| `test/02_integration/rendering/pixel_verify_browser_glass.spl` | genuine-merge | 153/153 | 231/231 | 0/0 |
| `test/02_integration/rendering/pixel_verify_full.spl` | genuine-merge | 163/163 | 209/209 | 0/0 |
| `test/02_integration/rendering/pixel_verify_main.spl` | genuine-merge | 100/100 | 143/143 | 0/0 |
| `test/02_integration/rendering/pixel_verify_scene.spl` | genuine-merge | 149/149 | 214/214 | 0/0 |
| `test/02_integration/rendering/pixel_verify_simple.spl` | genuine-merge | 128/128 | 176/176 | 0/0 |
| `test/02_integration/rendering/pixel_verify_style.spl` | genuine-merge | 55/55 | 74/74 | 0/0 |
| `test/02_integration/stats_command_spec.spl` | genuine-merge | 27/27 | 60/60 | 0/0 |
| `test/02_integration/storage/dbfs/dbfs_engine_checkpoint_ring_spec.spl` | style-difference | 91/91 | 111/111 | 14/14 |
| `test/02_integration/storage/dbfs/dbfs_engine_pager_spec.spl` | style-difference | 70/70 | 90/90 | 3/3 |
| `test/02_integration/storage/dbfs/dbfs_nvme_callback_spec.spl` | style-difference | 106/106 | 121/121 | 9/9 |
| `test/02_integration/storage/dbfs/dbfs_posix_shim_spec.spl` | style-difference | 96/96 | 112/112 | 1/1 |
| `test/02_integration/storage/dbfs/dbfs_ring_diag_spec.spl` | style-difference | 52/52 | 62/62 | 12/12 |
| `test/02_integration/t32_hw/50_session_close_spec.spl` | style-difference | 54/54 | 71/71 | 1/1 |
| `test/03_system/app/compiler/feature/world_units_newunit_spec.spl` | stale-use-only | 14/14 | 17/17 | 1/1 |
| `test/03_system/app/native_build/feature/executable_size_reduction_spec.spl` | style-difference | 38/38 | 50/50 | 3/3 |
| `test/03_system/app/os/feature/ui_access_protocol_spec.spl` | stale-use-only | 136/136 | 151/151 | 1/1 |
| `test/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl` | style-difference | 29/29 | 34/34 | 2/2 |
| `test/03_system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl` | style-difference | 32/32 | 35/35 | 1/1 |
| `test/03_system/compiler/vhdl_source_facade_spec.spl` | genuine-merge | 674/674 | 809/809 | 0/0 |
| `test/03_system/feature/lib/mcp/bootstrap_e2e_test.spl` | stale-use-only | 50/50 | 69/69 | 3/3 |
| `test/03_system/feature/lib/mcp/bootstrap_import_test.spl` | stale-use-only | 19/19 | 32/32 | 3/3 |
| `test/03_system/feature/lib/mcp/bootstrap_protocol_test.spl` | style-difference | 63/63 | 91/91 | 1/1 |
| `test/03_system/feature/lib/minimal_spec.spl` | style-difference | 15/15 | 43/43 | 2/2 |
| `test/03_system/feature/scilib/cuda_device_buffer_spec.spl` | style-difference | 702/702 | 728/728 | 1/1 |
| `test/03_system/feature/scilib/linalg_backend_diagnostics_spec.spl` | style-difference | 65/65 | 70/70 | 1/1 |
| `test/03_system/feature/scilib/linalg_cuda_backend_spec.spl` | style-difference | 299/299 | 372/372 | 1/1 |
| `test/03_system/feature/scilib/linalg_openblas_backend_spec.spl` | style-difference | 84/84 | 96/96 | 1/1 |
| `test/03_system/feature/scilib/linalg_simd_spec.spl` | style-difference | 151/151 | 169/169 | 9/9 |
| `test/03_system/feature/scilib/linalg_torch_backend_spec.spl` | style-difference | 1500/1500 | 1597/1597 | 1/1 |
| `test/03_system/feature/scilib/ndarray_broadcast_spec.spl` | style-difference | 311/311 | 392/392 | 57/57 |
| `test/03_system/feature/scilib/ndarray_dtype_spec.spl` | style-difference | 88/88 | 138/138 | 2/2 |
| `test/03_system/feature/scilib/ndarray_reduction_spec.spl` | style-difference | 49/49 | 61/61 | 4/4 |
| `test/03_system/feature/scilib/ndarray_simd_spec.spl` | style-difference | 119/119 | 166/166 | 14/14 |
| `test/03_system/feature/scilib/ndarray_ufunc_spec.spl` | style-difference | 179/179 | 204/204 | 30/30 |
| `test/03_system/feature/scilib/simd_f32_spec.spl` | style-difference | 53/53 | 63/63 | 1/1 |
| `test/03_system/feature/usage/aop_architecture_rules_spec.spl` | style-difference | 135/135 | 305/305 | 1/1 |
| `test/03_system/feature/usage/aop_spec.spl` | style-difference | 223/223 | 408/408 | 3/1 |
| `test/03_system/feature/usage/btree_basic_spec.spl` | style-difference | 60/60 | 88/88 | 1/1 |
| `test/03_system/feature/usage/cmm_lsp/bulk_validate_spec.spl` | genuine-merge | 309/309 | 455/455 | 0/0 |
| `test/03_system/feature/usage/cmm_lsp/cmm_lexer_spec.spl` | genuine-merge | 359/359 | 539/539 | 0/0 |
| `test/03_system/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl` | genuine-merge | 74/74 | 181/181 | 0/0 |
| `test/03_system/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl` | genuine-merge | 354/354 | 539/539 | 0/0 |
| `test/03_system/feature/usage/cmm_lsp/cmm_parser_spec.spl` | genuine-merge | 362/362 | 538/538 | 0/0 |
| `test/03_system/feature/usage/cmm_lsp/string_efficiency_spec.spl` | genuine-merge | 452/452 | 592/592 | 0/0 |
| `test/03_system/feature/usage/contract_persistence_feature_spec.spl` | style-difference | 68/68 | 149/149 | 1/1 |
| `test/03_system/feature/usage/effect_system_spec.spl` | style-difference | 222/222 | 439/439 | 2/3 |
| `test/03_system/feature/usage/exists_check_spec.spl` | style-difference | 98/98 | 148/148 | 14/14 |
| `test/03_system/feature/usage/extern_functions_spec.spl` | style-difference | 66/66 | 135/135 | 10/10 |
| `test/03_system/feature/usage/hashmap_basic_spec.spl` | style-difference | 61/61 | 100/100 | 1/1 |
| `test/03_system/feature/usage/llvm_backend_aarch64_spec.spl` | style-difference | 62/62 | 78/78 | 3/3 |
| `test/03_system/feature/usage/llvm_backend_arm32_spec.spl` | style-difference | 60/60 | 76/76 | 2/2 |
| `test/03_system/feature/usage/llvm_backend_i686_spec.spl` | style-difference | 64/64 | 81/81 | 3/3 |
| `test/03_system/feature/usage/llvm_backend_riscv32_spec.spl` | style-difference | 64/64 | 79/79 | 2/2 |
| `test/03_system/feature/usage/llvm_backend_riscv64_spec.spl` | style-difference | 64/64 | 79/79 | 2/2 |
| `test/03_system/feature/usage/math_autograd_runtime_spec.spl` | style-difference | 100/100 | 162/162 | 2/2 |
| `test/03_system/feature/usage/math_dl_equations_spec.spl` | style-difference | 346/346 | 466/466 | 1/1 |
| `test/03_system/feature/usage/no_paren_calls_spec.spl` | genuine-merge | 235/235 | 538/538 | 0/1 |
| `test/03_system/feature/usage/wasm_compile_spec.spl` | stale-use-only | 261/261 | 323/323 | 1/1 |
| `test/03_system/gui/glass_pixel_compare_spec.spl` | style-difference | 122/122 | 182/182 | 3/3 |
| `test/03_system/gui/tui_screen_spec.spl` | style-difference | 93/93 | 137/137 | 5/5 |
| `test/03_system/gui/web_api_json_spec.spl` | style-difference | 51/51 | 64/64 | 5/5 |
| `test/03_system/interpreter/interpreter_bugs_spec.spl` | style-difference | 126/126 | 227/227 | 1/1 |
| `test/03_system/os/boot_smoke_spec.spl` | style-difference | 155/155 | 208/208 | 2/2 |
| `test/03_system/os/port/alt_rootfs_disk_boot_spec.spl` | style-difference | 96/96 | 124/124 | 1/1 |
| `test/03_system/tools/deploy/smoke_spec.spl` | style-difference | 33/33 | 47/47 | 12/12 |
| `test/05_perf/bench/db_accel_index/db_accel_index_spec.spl` | style-difference | 270/270 | 346/346 | 1/1 |
| `test/05_perf/graphics_2d/bench_2d_metal_simple_jit.spl` | style-difference | 162/162 | 243/243 | 2/2 |
| `test/05_perf/graphics_2d/vulkan_spirv_spec.spl` | style-difference | 79/79 | 116/116 | 4/4 |
| `test/05_perf/llvm_lib_ffi_perf_spec.spl` | genuine-merge | 219/219 | 269/269 | 0/0 |
| `test/05_perf/local_gpu_check/run_gpu_check.spl` | style-difference | 135/135 | 167/167 | 1/1 |
| `test/05_perf/tauri_equiv/report_spec.spl` | style-difference | 175/175 | 252/252 | 2/2 |
| `test/05_perf/ui_access/ui_access_hot_paths_spec.spl` | stale-use-only | 105/105 | 131/131 | 1/1 |

## Overlap (unchanged, from I4)

| numbered | legacy | shared | identical | divergent | only-numbered | only-legacy |
|---|---|---|---|---|---|---|
| `test/01_unit` | `test/unit` | 5096 | 4253 | 843 | 2490 | 7 |
| `test/03_system/feature` | `test/feature` | 367 | 286 | 81 | 404 | 2 |
| `test/02_integration` | `test/integration` | 633 | 544 | 89 | 181 | 0 |
| `test/03_system` | `test/system` | 349 | 287 | 62 | 3168 | 1589 |
| `test/05_perf` | `test/perf` | 128 | 110 | 18 | 77 | 7 |
| `test/04_smoke` | `test/smoke` | 1 | 1 | 0 | 6 | 0 |

## Why this file exists (unchanged)

`test/` carries TWO parallel trees: numbered (`test/01_unit`, `test/03_system`, …)
and legacy (`test/unit`, `test/system`, …). They are NOT byte-identical — the
common assumption that they are is false and would make a delete-legacy sweep
destructive.

**Both trees execute.** `src/app/test_runner_new/` has no path allowlist and no
legacy exclusion; the default root is `test/` (`test_runner_main.spl:209`),
recursive. Every duplicated spec runs twice, so full-suite counts and timings
are inflated by roughly the overlap (~5,500 files).

`test/FILE.md` lists ONLY the numbered dirs in its Allowed Entries table, so the
legacy dirs are undeclared migration residue, not a deliberate compat path.

`test/03_system/os_crypto_ref_helpers.spl` is a deliberate compat re-export shim,
not a stub — permanently excluded (J4 FINDING 2).

## Correct sequence

1. Close Worklist B (61) and the `stub-legacy`/`stale-use-only` rows of A and C
   unmerged — no file needs opening.
2. Hand-merge Worklist A `genuine-merge`, then `style-difference` by two-way read.
3. Triage Worklist C, then the ~1,600 legacy-only paths.
4. Re-hash to prove 100% identity.
5. Delete legacy with `sh scripts/check/check-tree-size-push.shs --expect-files <n>`.

---

## Step-1 execution log — stream J4 (2026-08-10)

Binary for all verdicts: `src/compiler_rust/target/bootstrap/simple` (33,653,056 bytes, mtime 2026-08-09 23:10).

### FINDING 1 — the line-count proxy is wrong for 64 of the 145 entries (44%)

Re-measuring with **code lines** (non-blank, non-`#`) instead of raw lines flips
64 entries: the legacy file is NOT ahead. **54 of those 64** legacy files are
PENDING/DISABLED specs — the body is commented out and replaced by an
`it "skipped"` / `pending_reason` stub. Their raw line count is high only
because the dead code is retained as comments. 0 of the 81 genuinely-ahead
files carry that marker, so the split is clean.

The worklist's flagship example is in the disproven set:
`test/unit/app/diagram/filter_spec.spl` (199 lines) is 4 lines of `it "skipped"`
plus 195 lines of commented-out code. The 11-line numbered twin is a real,
executing API-presence spec. Merging legacy over it would have been a regression.

### FINDING 2 — `test/03_system/os_crypto_ref_helpers.spl` is not a stub

The 6-line numbered file is a deliberate compat re-export shim; the 311-line
implementation already lives at `test/03_system/os/os_crypto_ref_helpers.spl`.
Overwriting the shim with legacy content breaks every importing spec.
REMOVE from the worklist.

### FINDING 3 — the dominant "legacy ahead by 1-2 lines" delta is a STALE IMPORT

For 7 pairs the entire legacy-only content is `use std.test.*` (or
`use std.test.{describe, it, expect}`) — an import the numbered tree deliberately
removed. Restoring it makes the spec fail to load: exit 1 and **no verdict line at
all** (the spec runs nothing). Verified on
`test/01_unit/compiler/blocks/builder_api_basic_spec.spl`. Same for
`test/01_unit/app/todo/todo_parser_spec.spl`, whose legacy-only line is
`use tooling.TodoItem.*` — merged it went rc=1/no-verdict against a green
`executed=1 passed=1` baseline. All 8 merges were reverted.

### FINDING 4 — numbered "stubs" are a different test STYLE, not placeholders

Many short numbered twins are source-grep API-presence specs
(`rt_file_read_text(...)` + `expect(source).to_contain(...)`). They are weak
oracles, but they are not empty, and the legacy behavioural spec is frequently the
one that is stale. `test/02_integration/lib/std/doctest/discovery_spec.spl` is the
clearest case: the legacy file imports `std.doctest.discovery`, which does not
exist anywhere under `src/lib`. The numbered rewrite targets the real
`std.common.doctest.parser`. Legacy is dead code; do not merge.

### Merged and verified (kept)

Selection rule: legacy is a strict superset in CODE lines (numbered contributes
zero unique code lines), AND the added content is real test material rather than
an import.

| numbered file | verdict after merge | note |
|---|---|---|
| `test/01_unit/lib/crypto/sha256_x4_spec.spl` | `declared>=7 executed=7 passed=7 failed=0` | fixes a BROKEN import: numbered pulled `sha256_x4` from `std.crypto.sha256`, which does not define it (it lives in `sha256_simd`, no re-export). Unresolved `use` only WARNs, so this was silently wrong. |
| `test/01_unit/browser_engine/net/cookie_store_spec.spl` | `declared>=32 executed=32 passed=32 failed=0` | +3 examples over the 29-example baseline |
| `test/01_unit/compiler/u32_array_index_shr_spec.spl` | `declared>=6 executed=6 passed=6 failed=0` | +1 example (AC-1b2 dynamic `[u32; count]` repeat) |
| `test/01_unit/lib/common/result_ce_spec.spl` | `declared>=27 executed=27 passed=27 failed=0` | |
| `test/03_system/feature/usage/string_interpolation_spec.spl` | `declared>=15 executed=15 passed=15 failed=0` | +1 example (inline conditional in interpolation) |
| `test/01_unit/lib/common/string_core_ops_spec.spl` | `declared>=205 executed=205 passed=180 failed=25` | both merged examples PASS; the 25 failures are PRE-EXISTING at origin (`str_index_of`/`str_last_index_of` return -1 unconditionally, `str_ends_with` returns 0) |

`test/01_unit/lib/driver/null_block_driver_test.spl` was a no-op (the pair is
already identical once the copy is applied).

### Reverted after verification (8) — merging made them WORSE

`builder_api_basic`, `builder_default_parser`, `easy_api_basic`,
`testing_framework`, `utils_basic` (all `test/01_unit/compiler/blocks/`),
`compiler/mono/monomorphize_integration`, `compiler/parser/match_empty_array_bug`,
and `app/todo/todo_parser` — see FINDING 3. All eight now byte-match origin.

### Newly-RED finding filed

`doc/08_tracking/bug/parser_rejects_pub_union_after_attribute_2026-08-10.md` —
`@doc(...)` + `pub union` is a hard parse error (`expected Fn, found Union`)
while `pub enum` works. The legacy spec covered it; the numbered twin had the
coverage deleted instead of the bug fixed.

### What remains (139 of 145)

6 entries merged, 139 untouched. Of those 139: **64 are DISPROVEN** (FINDING 1 —
close them, do not merge) and **75 need per-file hand merges**. In the near-equal
band the numbered tree is usually the correct side even when it is shorter
(stale imports, superseded module paths, corrected semantics), so this residue
cannot be swept — every one needs the two-way read.

Recommended next step: re-derive the worklist on the CODE-line metric with the
pending-marker filter applied, which cuts 145 to 81 before any file is opened.
