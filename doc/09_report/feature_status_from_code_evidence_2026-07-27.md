# Feature Status Derived From Code Evidence — 2026-07-27

**Question answered:** how many features in `doc/02_requirements/feature/` remain to
implement, judged from **code evidence only** — not from the docs' own prose or
`**Status` markers.

## Method

1. Enumerated `doc/02_requirements/feature/*.md`. 53 directory entries = **51 feature
   docs** + `README.md` (not a feature) + `category/` (a taxonomy directory of 9 files,
   not requirement docs). The commonly-quoted "52" counts `README.md`.
2. Built a path index of 49,646 files under `src/`, `test/`, `doc/06_spec/`
   (`vendor/` excluded per the Owned-Code Scope rule).
3. For each doc, extracted its identity: slug tokens plus every backticked
   path/symbol it names (330 lines of extracted identifiers across 51 docs — an
   average of ~5 concrete identifiers per doc, and 6 docs name **zero**).
4. Matched each feature against `src/` (implementation), `test/` (spec), and
   `doc/06_spec/` (generated manual). Where the slug was ambiguous or produced no
   hit, fell back to grepping the doc's own named symbols.
5. Classified conservatively. "Implemented" requires a file or symbol match, never
   an inference from the doc's prose.

### Method limits (read before trusting a row)

- **A file whose name matches a feature is evidence of work, not of correctness.**
  No build or test was run for this report (machine load ~54, and the task forbade it).
  Every IMPLEMENTED+TESTED row means "impl file + spec file exist on disk", not
  "spec passes today".
- `doc/08_tracking/test/test_result.md` is ~69 days stale and
  `doc/02_requirements/feature/{feature,pending_feature}.md` and
  `doc/08_tracking/test/test_db.sdn` are **missing**, so no pass/fail record could
  corroborate any row.
- Plan-file checkbox progress turned out to be unusable: of all
  `doc/03_plan/agent_tasks/*.md`, **only two files use checkboxes at all**
  (`engine2d_four_backend_capture` 9/10, `office_cli_tui_ui_access` 0/11). Checkbox
  progress is therefore not a status signal in this repo.

## Per-feature table

Legend — **IT** = IMPLEMENTED+TESTED, **IU** = IMPLEMENTED-UNTESTED,
**P** = PARTIAL, **NS** = NOT-STARTED, **U** = UNDETERMINABLE.

| # | Feature doc | Class | Evidence (found, or searched-and-absent) | Contradicts declared status? |
|---|---|---|---|---|
| 1 | browser_wasm_webgpu_infra_options | **P** | FOUND `src/lib/gc_async_mut/gpu/browser_engine/script/js_transpiler.spl`, `script_runner.spl`, `web/browser_session_loading.spl` (all carry `type="text/simple"`, the doc's Option-A marker); spec `test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl` + manual. NOT FOUND: any WebGPU-processing-codegen module (Option B/C). Options doc with **no recorded selection** | no marker |
| 2 | cosmos_openssd_production_hal | **IT** | `src/os/kernel/arch/arm32/cosmos/` (16 files: `cosmos_fsbl.c`, `cosmos_ftl.c`, `cosmos_ftl_nfc_backend.c`, `cosmos_mmu_cache.c`, …); 17 tests incl. `test/02_integration/os/cosmos/cosmos_ftl_contract_test.c`, `test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl`; manual in `doc/06_spec/` | no marker |
| 3 | custom_type_iterator_protocol | **NS** | Searched `__iter__`, `iterator_protocol`, `iter_protocol` → **0 hits in `src/`, 0 in `test/`**. The only occurrences are *workaround comments citing the open bug*: `src/lib/common/bytes/span.spl:121` and `src/lib/common/search/types.spl:17` both reference `for_in_custom_struct_no_iterator_protocol_2026-06-15` | no marker |
| 4 | engine2d_four_backend_capture | **IT** | 73 src / 60 test / 27 spec matches: `src/lib/gc_sync_mut/gpu/engine2d/backend{,_baremetal,_cpu}.spl`, `src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl`; `test/02_integration/rendering/engine2d_backend_spec.spl`. Plan 9/10 checked | no marker |
| 5 | gpu_web_db_offload | **IT** | `src/lib/nogc_sync_mut/web_db_offload/{__init__,contract,device_backend}.spl`, `database/db_offload.spl`; `test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl` + unit contract spec + 2 manuals | no marker |
| 6 | host_gpu_lane | **IT** | `src/os/kernel/ipc/host_gpu_ivshmem_map.spl`, `src/os/kernel/arch/x86_64/host_gpu_ivshmem_vmm.spl`, `src/compiler_rust/compiler/src/interpreter_extern/host_gpu_lane.rs`; 21 specs, 18 manuals | no marker |
| 7 | llm_caret_claude_cli_full_parity | **IT** | `src/app/llm_caret/` (875 path matches incl. `chat.spl`, `server.spl`, `redact.spl`, `types.spl`); 63 specs; 34 manuals | no marker |
| 8 | llm_caret_claude_cli_harden | **IT** | Same `src/app/llm_caret/` tree; `test/04_smoke/llm_caret_cli_tui_hardening_smoke.spl` | no marker |
| 9 | llm_caret_gui_backends | **IT** | `src/app/llm_caret/{gui.spl,gui_metal.spl,gui_native_model.spl}`; `test/03_system/app/llm_caret/feature/llm_caret_gui_backends_spec.spl` + manual | no marker |
| 10 | llm_runtime_vllm_torch_interface | **IT** | `src/app/slang_pack/{core,main}.spl`, `src/lib/gc_sync_mut/slang/`, `src/app/llm_dashboard/collectors/vllm_control_panel.spl`; 56 specs; 66 manuals | no marker |
| 11 | llm_runtime_vllm_torch_interface_options | **IT** | Options doc for #10; same evidence. Duplicate identity — inflates any naive count | no marker |
| 12 | llm_tooling_context_ponytail_mimic | **IT** | `src/app/ponytail/{__init__,audit}.spl`, `src/lib/common/ponytail/`; `test/03_system/app/tooling/feature/context_ponytail_mimic_spec.spl`, `test/01_unit/app/tooling/ponytail_audit_spec.spl` | no marker |
| 13 | llm_tooling_context_ponytail_mimic_options | **IT** | Options doc for #12; same evidence. Duplicate identity | no marker |
| 14 | llm_tool_runtime_hardening | **IT** | Every path the doc names exists: `src/app/llm_caret/opencode_cli.spl`, `src/app/llm_runtime/serve_plan.spl`, `test/01_unit/app/llm_caret/opencode_cli_spec.spl`, `test/01_unit/app/llm_runtime/vllm_readiness_spec.spl`, both `doc/06_spec/` manuals. Best-specified doc in the set | no marker |
| 15 | low_dependency_ui_dynsmf | **IT** | `src/os/smf/dynsmf_session.spl`, `src/app/startup/dynsmf_autoload.spl`, `src/lib/common/ui/html_ui/dynsmf_entry.spl`; `test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl` +3 | no marker |
| 16 | low_dependency_ui_dynsmf_tldr | **IT** | TL;DR of #15; same evidence. Duplicate identity | no marker |
| 17 | multicore_green | **IT** | `src/lib/nogc_async_mut/concurrent/multicore_green.spl`; 49 test files incl. 4 named fixtures; 24 manuals under `doc/06_spec/05_perf/stress/` | no marker |
| 18 | nvme_base_spec_commands | **IT** | 40 src (`src/os/kernel/boot/c_nvme_adapter.spl`, `freestanding_nvme_adapter_contract.spl`, `cosmos_nvme_admin.c`, …); 75 tests; 39 manuals | no marker |
| 19 | office_cli_tui_ui_access | **IT** | `src/app/office/` (112 matches: `base_db.spl`, `launcher.spl`, `counter.spl`, …); 152 tests; 23 manuals. **But its plan file is 0/11 checked** — the only 0-progress plan in the repo, against a large implemented tree. Plan is stale, not the code | no marker |
| 20 | perf_profile_reporting | **IT** | REQ-PPR-006's validation exists: `test/05_perf/profile_scripts/profile_report_contract_test.shs` + `_negative_test.shs`; reports exist (`doc/09_report/pure_simple_profile_guided_executable_optimization_2026-06-01.md`, `profile_layout_native_smoke_evidence_2026-06-01.md`); `src/app/profiling/profile.spl`, `src/app/optimize/profile_layout_cli.spl`, `src/os/drivers/perf_report.spl`; README mentions profile 3x | no marker |
| 21 | production_gui_web_renderer_parity_hardening | **IT** | `src/app/wm_compare/production_gui_web_renderer_parity.spl`, `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl`; `test/03_system/check/production_gui_web_renderer_parity_{gate,evidence}_spec.spl` + manuals. No plan file | no marker |
| 22 | pure_simple_cli_completeness | **P** | REQ-003 names `walk_dir` → present in 31 src files, so the symbol exists; but the requirement is "the full CLI must **link** without unresolved `walk_dir` fallback", which is a **link-time property no static search can settle**. REQ-001/002/004/005 name no searchable symbol. Not verifiable without a build (forbidden here) | no marker |
| 23 | pure_simple_tool_infra_hardening | **IT** | `test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl` + `doc/06_spec/` manual. Note: REQs are behavioural (launcher rejects a seed binary, atomic swap+rollback, runner never converts failure to success) so the spec *is* the implementation surface | no marker |
| 24 | riscv32_riscv64_fpga_simpleos_production | **IT** | 129 src (`src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl`, `src/os/kernel/arch/riscv32/fpga_boot.spl`, `src/os/kernel/arch/riscv64/rv64_hosted_boot.spl`); 335 tests; 60 manuals | no marker |
| 25 | search_const_generic_dimension_2026-06-15 | **NS** | Searched `const_generic`, `ConstGeneric` → the *only* owned-code hit is a workaround comment at `src/lib/common/search/types.spl:351` that cites **this very requirement doc** as unfiled work. `src/compiler_rust/driver/src/cli/migrate/generics.rs` is unrelated migration tooling. 0 tests, 0 manuals | no marker |
| 26 | shared_multilingual_gpu_fonts | **IT** | `src/lib/common/gpu/font_atlas_composite.spl`, `src/lib/{nogc_sync_mut,nogc_async_mut}/engine/render/font_atlas.spl`, `src/app/test/shared_multilingual_gpu_fonts_rss_probe.spl`; `test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl` +9 | no marker |
| 27 | showcase_apps | **IT** | `src/lib/common/ui/showcase_catalog.spl`, `src/os/apps/showcase_catalog/{showcase_catalog,showcase_launch_action}.spl`; 23 tests; 20 manuals | no marker |
| 28 | simple_2d_renderdoc_backend_equivalence | **IT** | `src/app/test/renderdoc_{vulkan_capture,vulkan_widget_capture,replay_inspect,runtime_ops}.spl`; `test/03_system/check/gpu_rendering_vulkan_renderdoc_capture_spec.spl` +20; 28 manuals | no marker |
| 29 | simple_2d_vector_fonts | **IT** | `src/lib/{nogc_sync_mut,gc_sync_mut,nogc_async_mut,gc_async_mut}/text_layout/font_vector_data.spl`; `test/01_unit/lib/gpu/engine2d/vector_font_offload_spec.spl`, `test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl` | no marker |
| 30 | simple_2d_vector_fonts_tldr | **IT** | TL;DR of #29; same evidence. Duplicate identity | no marker |
| 31 | simple_3d_graph_ir | **IT** | `src/lib/{nogc_sync_mut,nogc_async_mut}/engine/render/graph_ir3d.spl`; `test/01_unit/lib/nogc_sync_mut/engine/render/graph_ir3d_spec.spl`, `test/01_unit/lib/engine/scene3d_spec.spl`. **0 generated manuals** in `doc/06_spec/` — spec exists but has evidently never been run through docgen | no marker |
| 32 | simple_erp | **IT** | `src/app/office/erp_bridge.spl`; `test/03_system/app/simple_erp/feature/simple_erp_{catalog,bigbiz,business_suite}_spec.spl`; manual `doc/06_spec/03_system/app/simple_erp/feature/simple_erp_catalog_spec.md`. (Naive `erp` grep is poisoned by `interp`; refined match used) | no marker |
| 33 | simpleos_filesystem_toolchain_servers | **P** | FOUND the doc's `/SYS/SIMPLETOOL.SDN` in `src/os/installer/image_builder.spl` and `src/os/port/initramfs_pack.spl`, with `test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl`; also `src/app/ci/build_simpleos_toolchain.spl`. NOT FOUND: any *server* module — searched `toolchain_server`, `fs_server`, `simpleos_toolchain` → 0 owned-code matches. The doc's other markers (`/usr/bin/clang`, `/usr/bin/simple --version`) are guest paths, not repo artifacts. No plan file | no marker |
| 34 | simpleos_memory_leveling | **IT** | `src/os/kernel/memory/memory_leveling{,_capabilities,_device_adapters}.spl`, `src/lib/nogc_sync_mut/memory_leveling.spl`; `test/02_integration/os/memory_leveling_{vmm_effects,dma_runtime,pmm_syscall_effects}_spec.spl`; manual | no marker |
| 35 | simpleos_memory_leveling_gpu_nic_dma | **P** | Base memory-leveling present (see #34) and `test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl` + manual exist. But the **one symbol this doc names**, `memory_leveling_apply_pressure`, returns **0 hits in `src/` and 0 in `test/`**. Spec-ahead-of-impl, or the doc names a symbol that was renamed without updating the requirement | no marker |
| 36 | simpleos_nvfs_submodule_migration | **IT** | The doc names `src/os/services/nvfs` → **exists** (`__init__.spl`, `core/`, `driver/`, `posix/`, `tool/`); plus `src/lib/nogc_sync_mut/fs/nvfs/{__init__,api,extent_map}.spl`; 84 tests; 14 manuals. Submodule origin `ormastes/simple-nvfs` not verified (no network use). No plan file | no marker |
| 37 | simpleos_qemu_host_gpu_2d | **IT** | `src/os/kernel/ipc/host_gpu_ivshmem_map.spl`, `src/os/kernel/arch/x86_64/host_gpu_ivshmem_vmm.spl`, `src/os/compositor/engine2d_wm_frame_executor.spl`; `test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl` + manual | no marker |
| 38 | simpleos_qemu_host_gpu_4k_capacity_options | **NS** | Options doc that states in its own second line "**User selection is required** before changing the existing 8 MiB requirement" — so no option is in force. Searched `gpu_4k_capacity`, `host_gpu_4k`, `4k_capacity`, `protocol_v2`, `33554432`/`32 * 1024 * 1024` in `src/os` and `src/lib/common/gpu` → **no protocol-v2 or 32 MiB arena evidence**. (`fat32_4k_compare`, `widget_showcase_4k_8k` are unrelated 4K hits.) No plan file | no marker |
| 39 | simple_web_browser_engine_production_hardening | **IT** | 142 src under `src/lib/gc_sync_mut/gpu/browser_engine/` (`webgl_context.spl`, `webgpu_context.spl`, `webgpu_commands.spl`, …); 161 tests; 28 manuals | no marker |
| 40 | simple_web_browser_production_hardening | **IT** | Slug does not name a src module, but the doc's named routes (`/api/state`, `/api/widgets`, `/ui/login`) resolve to `src/app/ui.web/{server,async_server,ui_routes,html}.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`, `test/03_system/security/simple_web_browser_engine_security_spec.spl` + manuals | no marker |
| 41 | simple_wm_host_simpleos_fullscreen | **IT** | Impl by behaviour, not by name: `src/os/compositor/compositor.spl`, `src/os/compositor/wm_scene.spl`, `src/os/desktop/shell.spl` carry fullscreen handling; specs `test/03_system/os/wm/simple_wm_host_fullscreen_spec.spl`, `test/03_system/check/{wm_production,simpleos_wm}_fullscreen_evidence*_spec.spl` (7) + 6 manuals. **Doc names zero concrete symbols** — classification rests on the spec names, not the doc | no marker |
| 42 | sound_engine | **IT** | `src/runtime/runtime_audio.c`, `src/lib/nogc_sync_mut/io/audio_sffi.spl`, `src/lib/nogc_sync_mut/engine/audio/{__init__,audio_group}.spl` (43 refined matches); `test/03_system/app/audio_group_spec.spl`, `test/01_unit/lib/engine/audio_bus_spec.spl`; 4 manuals. (Naive `sound` grep is poisoned by `test/cert/soundness/`) | no marker |
| 43 | sqlite_vfs_contract | **P** | FOUND contract layer: `src/lib/nogc_sync_mut/io/sqlite_sffi.spl`, `src/app/io/sqlite_{ffi,sffi}.spl`, `src/runtime/runtime_sqlite.c`, and `test/01_unit/os/port/sqlite_vfs_contract_spec.spl`. NOT FOUND: no `sqlite3.c` amalgamation anywhere in the tree, and **no `sqlite3_vfs` / `vfs_register` symbol in `runtime_sqlite.c`** — the VFS itself is unwritten. 0 generated manuals | **no** — declared `**Status:** In Progress (contract only — no SQLite build yet)` is *exactly right*; this is the one accurate marker in the set |
| 44 | sspec_scenario_manual | **NS** | The doc's own "already implemented" table is accurate (`src/app/spipe_docgen/spipe_docgen/parser.spl` has `@manual` handling; `tui_captures` present in 3 src / 4 test). But **all five requested gaps are absent**: `protocol_capture` 0, `--audience=user` 0, `@user_facing` 0, `capture_keymap` 0, text-grid capture 0 — in both `src/` and `test/`. FR-1..FR-5 = the actual ask = not started. No plan file | no marker |
| 45 | ui_cli_llm_access | **IT** | Doc's named error taxonomy resolves in code: `win_text_access` (34 src files), `target_not_found` (7), `stale_target` (7), `unsupported_action` (4); specs `test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access{,_final_review}_spec.spl` + 2 manuals; `.spipe/ui_cli_llm_access` state | declared `**Status:** Selected requirements` — stale but not false |
| 46 | unified_optimizer_plugin | **IT** | `src/compiler/60.mir_opt/optimizer_plugin.spl` (a real registry: "Generalizes MIR optimizer, source-level optimizer, and hotspot optimizer behind a common interface"); `test/01_unit/compiler/mir/optimizer_plugin_spec.spl` + `optimizer_plugin_adapter_test.spl` | **YES (understates)** — declared `**Status:** Proposed`, but it is implemented and specced. 0 generated manuals |
| 47 | update_tuf_trust | **P** | FOUND `src/os/services/update/{tuf_metadata,tuf_signing}.spl` (+ `slsa_provenance.spl`); spec exists for metadata only: `test/01_unit/os/services/update/tuf_metadata_spec.spl`. **`tuf_signing.spl` has no spec**, 0 generated manuals, no plan file | declared `**Status:** Model (Phase 5 groundwork)` — consistent |
| 48 | var_resolution_rules | **IT** | `src/compiler/99.loader/module_resolver/var_resolution.spl`; `test/01_unit/compiler/module_resolver/var_resolution_spec.spl` | **YES (understates)** — declared `**Status:** requirements / canonical spec (verbatim from request, annotated)`, i.e. reads as not-yet-built, but impl + spec both exist. 0 generated manuals |
| 49 | wm_glass_theme_host_simpleos | **IT** | `src/os/compositor/{glass_dispatch,glass_effects,glass_effects_pure}.spl`, `src/lib/nogc_sync_mut/ui/glass/stitch_design_md.spl` (21 src); `test/integration/rendering/glass_render_e2e_spec.spl` +38; 13 manuals | no marker |
| 50 | wm_glass_theme_host_simpleos_tldr | **IT** | TL;DR of #49; same evidence. Duplicate identity | no marker |
| 51 | wm_gui_web_2d_host_env_hardening | **IT** | `src/lib/common/ui/host_env_contract.spl`, `src/app/test/test_host_env.spl`; `test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl`, `test/01_unit/lib/common/ui/host_env_contract_spec.spl` + 3 manuals; `.spipe/wm_gui_web_2d_host_env_hardening` state | no marker |

## Bottom line

| Classification | Count | Share |
|---|---|---|
| IMPLEMENTED+TESTED | **41** | 80% |
| IMPLEMENTED-UNTESTED | **0** | 0% |
| PARTIAL | **6** | 12% |
| NOT-STARTED | **4** | 8% |
| UNDETERMINABLE | **0** | 0% |
| **Total feature docs** | **51** | |

**Remaining to implement: 10 of 51** — 4 not started, 6 partial.

- **NOT-STARTED (4):** `custom_type_iterator_protocol`,
  `search_const_generic_dimension_2026-06-15`,
  `simpleos_qemu_host_gpu_4k_capacity_options`, `sspec_scenario_manual`.
- **PARTIAL (6):** `browser_wasm_webgpu_infra_options`,
  `pure_simple_cli_completeness`, `simpleos_filesystem_toolchain_servers`,
  `simpleos_memory_leveling_gpu_nic_dma`, `sqlite_vfs_contract`, `update_tuf_trust`.

Adjusting for the **5 duplicate docs** (`*_tldr` and `*_options` files that restate a
sibling: #11, #13, #16, #30, #50), the set describes **46 distinct features**, of which
**10 remain**.

Zero features landed as IMPLEMENTED-UNTESTED — every feature with an implementation
also has at least one spec file. The gap in this repo is not missing specs; it is
**missing status bookkeeping**.

## Contradictions with declared status

Only **5 of 51** feature docs carry a `**Status` marker at all
(`sqlite_vfs_contract`, `ui_cli_llm_access`, `unified_optimizer_plugin`,
`update_tuf_trust`, `var_resolution_rules`). Of those:

- **2 contradict the code — both by *understating*:**
  - `unified_optimizer_plugin` — says **Proposed**; is implemented
    (`src/compiler/60.mir_opt/optimizer_plugin.spl`) and specced (2 tests).
  - `var_resolution_rules` — says **requirements / canonical spec**; is implemented
    (`src/compiler/99.loader/module_resolver/var_resolution.spl`) and specced.
- **3 are consistent** — `sqlite_vfs_contract` is notably precise ("contract only —
  no SQLite build yet" matches the absent `sqlite3_vfs`), `update_tuf_trust` and
  `ui_cli_llm_access` are stale but not false.

**No doc claims completion that the code refutes.** The dangerous direction here is the
opposite of what was feared: the repo *under-reports* its own progress, so the 46
undeclared docs are the real risk — a reader has no way to tell #46 (built, shipped)
from #44 (not started) without a scan like this one.

## Stage-4 bootstrap gating

Requested check: which features are "implemented but unqualifiable" because they are
gated on the stage-4 self-hosted bootstrap (never green on Linux x86_64).

**Answer: exactly one feature doc mentions bootstrap at all** —
`pure_simple_tool_infra_hardening` (its REQ-001 rejects "a Rust bootstrap seed or
debug binary presented as the deployed `simple` runtime"). That is a *guard against*
the seed, not a dependency on stage-4.

So no feature in this set is doc-declared stage-4-gated. This is a **traceability gap,
not a clean bill of health**: the stage-4 wall is a well-documented recurring blocker
elsewhere in the repo, and the fact that no requirement doc records a dependency on it
means the "implemented but unqualifiable" state is currently *invisible* at the
requirements layer. Any feature above whose verification runs through the deployed
self-hosted binary inherits that risk silently.

## Findings about doc quality (the meta-result)

1. **169 of 186 requirement docs (feature+NFR) carry no `**Status` marker.** In
   `feature/` specifically it is 46 of 51. Status is not tracked in this repo.
2. **Acceptance-criteria checkboxes are unused** — 3 across all 186 docs.
3. **Plan-file checkboxes are equally unusable** — only 2 of all
   `doc/03_plan/agent_tasks/*.md` files use them at all.
4. **The auto-generated status artifacts are missing or stale.**
   `doc/02_requirements/feature/feature.md` and `pending_feature.md` — which
   `.claude/rules/structure.md` promises are regenerated *every test run* — do not
   exist, nor does `doc/08_tracking/test/test_db.sdn`; `test_result.md` is ~69 days
   old. **This is itself strong evidence that the full test suite has not completed
   in ~69 days**, which is the root cause of the unanswerable question.
5. **6 docs name zero searchable identifiers**, and the median doc names ~5. Docs like
   `simple_wm_host_simpleos_fullscreen` and `simpleos_qemu_host_gpu_2d` are only
   classifiable because *someone else* named a spec file after the slug.
6. **5 docs are duplicates** (`_tldr` / `_options` restatements), inflating any raw
   count by ~10%.
7. **`category/` is a taxonomy directory** (9 files: Codegen, Concurrency,
   Control_Flow, Data_Structures, Infrastructure, Language, Testing_Framework, Types,
   Uncategorized) sitting inside `feature/`, which is why directory-entry counts read
   53 rather than 51.

## Recommended next step

The cheapest durable fix is not to backfill 46 `**Status` markers by hand — it is to
get one full test run to complete so `feature.md` / `pending_feature.md` /
`test_db.sdn` regenerate. This report is a stopgap that a green suite makes obsolete.

## Companion artifact

`doc/02_requirements/feature/pending_feature.md` was regenerated from this scan,
listing only the 10 NOT-STARTED and PARTIAL entries. It is explicitly marked as
**scan-derived, not test-run-derived**, so that the next real test run overwrites it
without ambiguity.

---
*Generated 2026-07-27 by static code-evidence scan. No build or test was executed.
Verification of any single row is one `ls` away — the evidence paths are literal.*
