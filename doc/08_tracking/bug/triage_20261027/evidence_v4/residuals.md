# V4 residual review details

These 31 rows remain `needs_more_evidence`; no runtime attempt is admitted. Some have report/source review recorded. This is not a claim that every row is unreviewed.

## native_build_parser_rejects_module_level_var_init_2026-08-17 — native-build's parser rejects a module-level `var x: T = ...` the seed accepts

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_build_parser_rejects_module_level_var_init_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_decls_use.spl:449-474; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_build_entry_module_loses_own_class_methods_multimodule_2026-08-17.md#Two-prior-misdiagnoses; reviews/research_v2_12.md#native_build_parser_rejects_module_level_var_init_2026-08-17; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_build_entry_module_loses_own_class_methods_multimodule_2026-08-17.md:54-66; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_decls_use.spl:436-474
```
- Review rationale: The full original report quotes expected Fn/found Assign and claims an initializer bisect; the sibling full report explicitly says that exact text is absent from its 2153-line guard log and was already ablated. The target var parser expects Assign and parses an initializer, so merely adding initializer support is not a supported remedy. These could be different executions, but neither document binds a retained original log and exact source/compiler digest sufficient to resolve that identity conflict. Needs more: the original guard transcript containing the quoted parse failure, command/environment and source/compiler digest, plus the sibling 2153-line transcript identity. No rerun is needed or authorized to resolve the documentary attribution.
- Review corrections: Retain needs_more_evidence for the genuinely conflicting producer/log attribution; current source acceptance neither proves invalidity nor establishes a historical repair.

## ora_batch_aa_pre_existing_red_specs_2026-08-26 — ora_batch_aa specs RED at pre-edit baseline (sspec modernization batch)

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; validity `valid`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/ora_batch_aa_pre_existing_red_specs_2026-08-26.md:12-92; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/dma_driver_spec.spl:147-178; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/scheduler_isolation_spec.spl:137-168; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.spl:44-107,109-158; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/ora_batch_aa_pre_existing_red_specs_2026-08-26.md:12-92
```
- Review rationale: The full report is a multi-owner pre-edit baseline ledger, not one reproducible defect. Additional target inspection finds DMA/scheduler contain standalone print-PASS/FAIL functions rather than the claimed model-only shape, while the four JS reclamation scenarios all call an explicit fail("RED: generation-safe JS VM reclamation is not implemented") placeholder. That is concrete heterogeneity and changed source, not an aggregate modernization regression or shared remedy. Most other listed assertions/providers were not semantically audited in this bounded classification pass. Needs more: retained per-spec pre-edit source identity, command/runner/host and failure logs from /tmp/sspec_census/ora_batch_aa and /tmp/sspec_aa/pipeline.log, plus owner attribution for the remaining named assertion failures. Keep the historical ledger valid; do not qualify the whole inventory from these samples.
- Review corrections: Retain needs_more_evidence for the genuinely unfinished multi-spec attribution. Three inspected owners give new substantive evidence but do not stand in for the remaining failing-provider inventory.

## pre_push_hook_selftest_commits_fixtures_into_invoking_repo_2026-08-21 — Pre-push hook: a WIP guard's selftest commits fixtures into the invoking repo, hijacking HEAD

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; validity `valid`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/pre_push_hook_selftest_commits_fixtures_into_invoking_repo_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-guard-selftests-isolated.shs:54; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/pre-push-conflict-tree-guard.shs:74
```
- Review rationale: Full report claims static census plus dynamic HEAD-mutation protection. Current static scan strips comments and exempts any script containing git init or directed mutations, which is weaker than demonstrating every call targets a private repo. Current hook begins with repository-root identity guards, but target search found neither reported run_guard wrappers nor HEAD snapshot/hijack logic. This is a material conflict with the resolution claim, not proof of present selftest safety. Remaining gap: Trace rest of hook/successor guard executor and inherited GIT_DIR/GIT_WORK_TREE isolation; review incident guard fixture calls before accepting repaired classification.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## release_cli_dispatch_functions_missing_2026-09-07 — `simple release` dispatch calls 20 functions that exist nowhere

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/release_cli_dispatch_functions_missing_2026-09-07.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/release/main.spl:6-34,221-234,330-881,940-974; ancestry 0bfef5664ee
```
- Review rationale: All twenty-one report-named wrapper definitions now appear in main and authority imports exist. Inspected run_version_check validates arguments, calls check_repository_version and renders the actual result. This disproves continued absence of that adapter, but is not decisive invalidity of the historical report. Complete adapter bodies and dispatch smoke coverage remain to audit before declaring the whole multi-command incident fixed; no blanket fixed-pending claim.
- Review corrections: queue: validity valid -> uncertain; low research: inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## render_lane_specs_import_nonexistent_modules_2026-08-08 — Render-lane specs import modules that were never implemented (2026-08-08)

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/render_lane_specs_import_nonexistent_modules_2026-08-08.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/blink/entity/paint_artifact.spl:53-71; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/content/web_contents_spec.spl:46-73; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/cc/entity/layer_tree_host.spl:32-56; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/blink/layout/block_flow.spl:208-224
```
- Review rationale: Full report inventories 24 absent modules and weak content/isolation oracles. Current PaintArtifact implements data and count accessors; WebContents test now observes two stored chunks and final end index rather than only non-nil. Block-flow owner also exists, and layer host still clones pending tree. Therefore historical missing counts and weak-WebContents descriptions are stale. The complete 27-spec/API matrix and class-alias isolation are not qualified; keep uncertain rather than infer closure from module presence.
- Review corrections: queue: validity valid -> uncertain, inspection_level report_reviewed -> source_reviewed; low research: inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## riscv64_qemu_release_lineage_and_nonce_gap_2026-08-11 — RISC-V 64 QEMU Release Lineage and Nonce Gap

- Source receipt: `adjudication_v2_18`; inspection `report_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_qemu_release_lineage_and_nonce_gap_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/_QemuRunner/scenario_exec.spl:421; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/os/build-simpleos-riscv64-interpreter-kernel.shs:67
```
- Review rationale: The full report requires both admitted producer lineage and runner-correlated nonce for the FAT32 acceptance lane. A newer interpreter builder embeds nonce into interpreted source and still selects the seed; that is a different lane. Compiler-filesystem nonce handling likewise cannot qualify the reported canonical FAT32 run. Historical behavior remains diagnostic. Remaining gap: Locate canonical FAT32 receipt classifier and retained admitted producer/run receipt; adjacent nonce support is not a fix.
- Review corrections: research validity: valid -> uncertain; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## runtime_bundle_duplicate_gate_baseline_drift_2026-08-24 — Runtime bundle duplicate-symbol gate has unrelated baseline drift

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; validity `valid`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/runtime_bundle_duplicate_gate_baseline_drift_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-runtime-bundle-duplicate-symbols.shs:103; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/runtime_bundle_duplicate_symbols_baseline.txt:88; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:1111; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_thread.c:733
```
- Review rationale: Read full short report and actual gate extraction: it derives bundle source names, lexically scans definitions, and compares named pairs/body-agreement flags; it is not a linker-profile oracle. The rt_thread_sleep baseline still lists native/thread, while native intentionally lacks the definition and thread owns real sleep with worker-blocked accounting. This substantiates stale-row concern without establishing all twelve historical pairs. Remaining gap: Required 12-pair ownership/link-profile inventory is not supplied by the report and was not independently reconstructed in this pass. Next bounded step: derive exact target duplicate pairs from compiler source list, then inspect only those owner bodies and link profiles; no broad baseline edit or gate execution.
- Review corrections: queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## seed_interp_ecs_lower_and_freefn_closure_byref — Seed interpreter cannot lower ECS Entity/ComponentStore<T>; free-fn mutation lost inside

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_interp_ecs_lower_and_freefn_closure_byref.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/devfs_service.spl:44-83; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:174-200
```
- Review rationale: Report combines ECS type lowering and free-function mutation inside it closures. Devfs still owns ComponentStore-specialized fields and constructs them through generic new calls. Captured-function entry now clones an overlay, refreshes owner scope and preserves local shadowing; this is not evidence that called free-function mutation publishes back to captured class slots. Both exact ECS import/type resolution and captured-argument writeback remain separate unresolved checks. Direct me calls or seed-safe adapters cannot establish either root repair. Investigation remains incomplete: the actual ECS type resolver and captured free-argument publication path were not traced to the original fixtures.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_interp_explicit_i64_default_arg_poisons_render_backgrounds_2026-07-11 — Passing explicit i64 budget_ms arg to software_pixels renderer paints all backgrounds

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_interp_explicit_i64_default_arg_poisons_render_backgrounds_2026-07-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:2304-2323; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/special/objects.rs:112-128
```
- Review rationale: Report records pixel differences but explicitly labels marshalling as hypothesis and lacks a reduced value-sensitive control. Current public pixels wrapper uses literal default 10000 and forwards budget to software_result; a source comment says cross-module seed defaults must be call-site constants. That is a different default-resolution correction, not proof explicit i64 values caused white paint. Constructor scoring allows omitted defaults but does not settle regular-function/JIT argument encoding. Need default-versus-explicit-equal-value fixture with received budget and pixel counts, without clamping. Investigation remains incomplete: regular-function default/explicit argument marshalling has not been traced; constructor scoring is only a related path, not decisive evidence.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_segv_calling_newly_added_stdlib_function_2026-09-02 — Rust seed SEGVs when calling a NEWLY ADDED function in an existing stdlib module

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_segv_calling_newly_added_stdlib_function_2026-09-02.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/env/platform.spl:45; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/module_loader.rs:620; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_eval.rs:583
```
- Review rationale: The report records a Windows seed call-time SEGV for the added os_from_uname while detect_os/is_linux work, across visibility/export variations. Current detect_os keeps the uname branches inline; the added function/control pair was reverted. The current flatten pass tags free functions with their module owner, and interpreter registration recovers that attribute. This establishes changed registration machinery, but neither identifies the failing call target nor distinguishes JIT from interpreter dispatch for the original binary. Remaining evidence: Recover the exact added-function fixture and binary execution mode, then trace its registration and selected call target through the active dispatch. The owner-tag mechanism alone does not settle this case.

## sffi_authority_baseline_stale_after_gpu_bootstrap_2026-08-24 — SFFI authority baseline stale after GPU/bootstrap sync

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sffi_authority_baseline_stale_after_gpu_bootstrap_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/audit/sffi-call-authority-census.shs:1; Target-ancestry history: 4edef8fab8e
```
- Review rationale: The report requires the actual differing census row, after its initial SSpec/loader attributions were rejected. Current shell implementation performs its own Perl fn/me-body scan; it does not count SSpec it bodies. Its default maximum_missing is now 20976 rather than the reported 19503. Inspecting this scanner clarifies the changed metric but does not reconstruct the retained historical 19504-versus-19503 populations. No row-level table from the baseline producer was available in the assigned evidence. Remaining evidence: Retrieve baseline 454226301f5 scanner/tree-bound table and the retained post-fix table, identify the exact differing row and audit the threshold-change history. A newer/higher ceiling is not a remedy.
- Review corrections: Current threshold is 20976; report counts are historical. Classification remains incomplete because the mandatory row provenance comparison cannot be replaced by metadata.

## simpleos_native_build_entry_closure_codegen_defects_2026-07-17 — Entry-closure cranelift drops module-global call initializers, nils if-val hits, and

- Source receipt: `adjudication_v2_22`; inspection `report_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md:680; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md:1489; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/entry_closure_global_init_tests.rs:6
```
- Review rationale: Independent partial read covered C1-C8 opening, the stored-field discriminator and final DMA/ABI/skip updates. The final report explicitly says C8 BlockDevice is fixed and the retained mount skip is for a different FS-trait sentinel; the low proposal's unresolved-C8 summary is stale. Current C1 regression documentation also distinguishes entry-wrapper versus library initializers. The 103KB report's complete intermediate history and all eight current owner/test paths remain unreviewed, so no aggregate classification is admitted. Next: reconcile each C1-C8 correction chronologically with its exact target implementation, especially alias repair and FS-trait sentinel.
- Review corrections: Reject research summary that final C8 itself remains unfixed. Retain needs_more_evidence; partial current C1 evidence cannot stand for complete aggregate adjudication.

## simpleos_stage3_native_ast_mode_cache_segfault_2026-08-20 — Stage 3 native compiler corrupts cross-file parser state

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_stage3_native_ast_mode_cache_segfault_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:1146,1376-1395,2179,2192
```
- Review rationale: Read the final HIR lifetime and MIR inverse-index sections (674-780), and identified the earlier 1-673 chronology as still unreviewed in this adjudication. Target module_lowering.reindex_enum_variant_owners removes prior owner membership and inserts new leaf membership without duplicates; registration callers exist for module enums and built-in Result/Option. That substantiates the index mechanism but cannot settle earlier parser corruption, tuple carriers, transient scope, HIR persistence or observed slopes. The compound report must not be accepted merely from its latest remedy. Remaining evidence: Read report 1-673 in chronological sections and trace driver_hir_pipeline_lowering scope/promotions plus actual inverse-index lookup and retained prefix-slope receipt.
- Review corrections: Retain partial-source inspection; index presence alone does not close all compound subdefects.

## simpleos_target_native_image_continuity_2026-08-20 — SimpleOS target-native image continuity — artifact-gated

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_target_native_image_continuity_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/port/disk_image_bake.spl:100-124,192-205; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/installer/image_builder.spl:1161
```
- Review rationale: The full report claims distinct nonempty role bytes/digests and canonical manifest admission. The target disk_image_bake implementation instead enumerates compiler/interpreter/loader aliases then loads the SAME simple_path into every role in bake lines 192-205; a scoped port search found no admit-role/render-manifest successor. This materially conflicts with the report’s stated source continuity. No current image artifact or guest receipt was reviewed, and a different canonical installer may own production continuity. Exact git-object comparison found the inspected owner bytes identical between d805 inventory and c0 target; this conflict was not introduced solely by the review-target advance. Remaining evidence: Identify the actual canonical producer and compare report-era role-admission implementation/history with disk_image_bake and installer, then bind each target manifest to loaded bytes.
- Review corrections: Do not accept the report’s “source continuity implemented” claim against conflicting target bake code.

## simpleos_x86_64_baremetal_link_ud2_fault_symbol_2026-07-17 — C fallback and fatal UD2 hook are restored; post-restore SysV stack pad is covered by a focused contract, but guest QEMU evidence remains blocked by VirtioGpuDriver kernel compilation

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_x86_64_baremetal_link_ud2_fault_symbol_2026-07-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:14615-14646; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/x86_64/interrupt.spl:375-393
```
- Review rationale: Read all amendments through dynamic stack alignment/page-boundary proof. They claim restored weak C hook and fatal UD2 dispatch. Exact target baremetal_stubs._rich_fault_entry instead blindly adds2 to saved RIP and iretqs on both error-code branches; a scoped x86_64 search finds only the strong SPL definition, not C hook usage/fallback. The report’s asserted restored fault semantics materially conflict with the target. The absent C reference may suppress the old undefined-symbol symptom while reinstating unsafe recovery, which is neither a verified fix nor invalidity. Exact git-object comparison found the inspected owner bytes identical between d805 inventory and c0 target; this conflict was not introduced solely by the review-target advance. Remaining evidence: Inspect removal/transplant diff in target ancestry (88aac2ffe28/ae55a746719), confirm actual production translation unit/link roots and reconcile fatal-handler regression before classifying remedy.
- Review corrections: Do not accept restored weak fallback/dynamic alignment from report: target actual handler contradicts it.

## sosix_qemu_matrix_remaining_owners_2026-08-14 — RV64/x86_32/ARM32 SOSIX QEMU rows lack an admitted Stage-4 runner so no exit-37 reap

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_qemu_matrix_remaining_owners_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/abi/syscall_shim_positioned.spl:39-76; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/boot/boot_fs.spl:379-405; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-sosix-qemu-matrix.shs:153-225
```
- Review rationale: Read every owner row in the compound tracker. The shared matrix admission owner was reviewed for case23. Positioned-I/O subclaim has evolved: shim_positioned_install_backend_route_v1 adopts accepted owner state; boot_fs now calls it with Nvfs after mounting and refuses failure, and DBFS/NVFS transaction owners also call installation. Thus “no production owner installs” is stale. Individual RV64/x86_32/ARM32 strong-symbol and exit37/reap paths, external native receipts, and fd-pinned importer semantics were not independently traced, preventing aggregate adjudication. Remaining evidence: Review each table owner separately, beginning real FAT32/NVFS positioned backend dispatch plus authenticated installed service owner, then per-target lifecycle/media receipts and importer fd-pinning.
- Review corrections: Current boot install callers contradict blanket missing-install wording; no aggregate fix or accepted completion inferred.

## spec_imports_declared_nowhere_2026-08-04 — 1003 names imported by 294 spec files are declared nowhere in owned src/, only warned not

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_imports_declared_nowhere_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/module_loader_core.spl:650-680,920-942; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl:1-16
```
- Review rationale: Read methodology13-95, sabotage mechanism204-230 and final triage698-742; per-family inventories96-203 and231-697 remain unreviewed. Target module_loader_core, not module_loader_resolve, owns selective name binding: it loads the module, registers requested caller-owner bindings and calls warn_unprovided_use_names. That routine checks recorded/nonopaque module surface and emits eval_warnings/eprint without failing. Thus warning-only unknown names remain source-supported, but binding now has caller-specific logic and the historical1003-name/782-module census cannot be promoted to current facts. Remaining evidence: Read omitted family inventories and audit declarations/reexports/symlink semantics at target per family; retain separate narrowly scoped unknown-import mechanism assessment.
- Review corrections: Do not rubber-stamp historical census or treat path resolver as registration owner; broad inventory remains incomplete despite inspected warning mechanism.

## stage3_numeric_interpolation_slot_corruption_2026-08-13 — Numeric interpolation of rt_heap_registry_count overwrites the ast_gen_harden_slot array

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_numeric_interpolation_slot_corruption_2026-08-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_numeric_interpolation_slot_corruption_2026-08-13.md:3-32,80-140,142-152,162-185; src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1756-1795,1846-1863,2717-2744; src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl:827-880; frozen queues_v2/group26.csv; 
```
- Review rationale: Report preserves a raw slot-pointer ASCII corruption observation, then claims a segment-loss interpretation without reconciling why dropped text would replace an AST backing pointer. Current typed scalar rendering is relevant but does not resolve that contradiction. Need the cited Build9 GDB receipt and LLVM emitted call/store chain, not interpreter segment tests.
- Review corrections: Research uncertain/unknown retained but not accepted: native slot corruption versus interpreter segment loss is a material unresolved evidence conflict.

## stage3_parse_stalls_at_tail_43_files_2026-08-17 — Stage-3 parse costs >547s on its last 43 files (superlinear, not a hang)

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_parse_stalls_at_tail_43_files_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_parse_stalls_at_tail_43_files_2026-08-17.md:18-40,100-132,148-190,212-225; src/compiler/80.driver/driver_source_pipeline_parsing.spl:1488-1496,1534-1544; frozen queues_v2/group26.csv; 
```
- Review rationale: Read the explicit retraction: runtime-after-stage3 exists and sanity receipt is absent, which alone shows return before sanity, not completion of parse. Current per-file progress removes the old 64-file ambiguity but cannot prove the historical phase. Need preserved runtime-after-stage3, wait status and final parse/phase transition receipts.
- Review corrections: Do not accept the report's parse-completed inference from post-command bookkeeping alone; neither invalid closure nor a confirmed tail stall follows.

## test_only_functions_family_census_2026-08-04 — 197 test-only functions shipped in production modules; census is a floor, items unfiled

- Source receipt: `adjudication_v2_28`; inspection `report_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_only_functions_family_census_2026-08-04.md
```
- Review rationale: The family report distinguishes dead wrappers, legitimate test infrastructure, unwired features and false positives. Its 197 Rust survivors and later Simple census cannot be adjudicated from the supplied legacy effects path. Full census/caller reconciliation was not completed; next step is checking WASI capability-table producer and consumer, then each retained class-(ii) entry.
- Review corrections: validity: valid -> uncertain.  See independent rationale.

## theme_ipc_k2_review_hard_stop_2026-07-27 — Theme IPC K2 stays fail-closed: no accepted design, K2 transport unimplemented

- Source receipt: `adjudication_v2_28`; inspection `report_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/theme_ipc_k2_review_hard_stop_2026-07-27.md
```
- Review rationale: Read the complete K2 rejection report: rejected/unintegrated candidates and no executable admission; obsolete heading does not negate five ABI/state/copyout failures. Bounded src/os searches did not locate compatibility cases or RV32 syscall6 owner. Wire snapshots and K1 payload copying do not adjudicate installed dispatcher behavior. Next: locate actual installed x86/C/RV32 dispatch and state-threading owners before accepting a current classification.
- Review corrections: inspection_level: source_reviewed -> report_reviewed.  See independent rationale.

## theme_snapshot_catalog_review_hard_stop_2026-07-27 — theme snapshot catalog design fail-closed after three exhausted review cycles

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/theme_snapshot_catalog_review_hard_stop_2026-07-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/ui/wm_chrome_theme.spl:68-136,233-235; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/ui.browser/backend.spl:56-67
```
- Review rationale: Read full report and inspected current WM snapshot install/read and browser snapshot selection. apply_theme_render_snapshot_to_wm_chrome stores the snapshot directly; browser accepts matching id and cache hashes. This does not locate hosted catalog bootstrap or external-frame authorization. Next: trace bootstrap and frame acceptance after a theme switch; current candidate-level gap cannot be decided from cache identity.

## theme_snapshot_catalog_review_hard_stop_2026-07-27_tldr — Theme snapshot catalog hard stop — TLDR

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/theme_snapshot_catalog_review_hard_stop_2026-07-27_tldr.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/theme_snapshot_catalog_review_hard_stop_2026-07-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/ui/wm_chrome_theme.spl:68-136,233-235; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/ui.browser/backend.spl:56-67
```
- Review rationale: Read TLDR and full companion report. They describe rejected candidates rather than admitted catalog behavior. Shared current WM/browser inspection establishes mutable active snapshot selection but not frame authorization. Same missing bootstrap and external acceptance trace as full report; companion status is not invalid duplication.
- Review corrections: inspection_level: report_reviewed -> source_reviewed.  See independent rationale.

## tree_wipe_module_damage_census_2026-08-04 — tree-wipe left 39 truncated modules; only 3 restored, the rest still short of their

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tree_wipe_module_damage_census_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/format_utils.spl:1-155; historical ae55a746719 inspected via git log bound to c0b3ad911f4cb00c0f3550b05baa8d06347d17d0
```
- Review rationale: Read census method, restoration limits and remaining-target ledger; current format_utils implements real padding/number formatting and history records ae55a746719 restoration after a wipe. This is not proof of canonical tier ownership or of all remaining destroyed/truncated modules. Middle per-file restoration ledger and blob-to-successor reconciliation were not completed. Next: reconcile format_utils exported consumers and historical body, then retained truncation candidates without overwriting divergent rewrites.
- Review corrections: validity: valid -> uncertain; inspection_level: report_reviewed -> source_reviewed.  See independent rationale.

## twelve_verification_assurance_specs_broken_not_flaky_2026-08-21 — 12 verification/assurance specs are stably broken, not flaky — and one is a parser defect

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/twelve_verification_assurance_specs_broken_not_flaky_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/00.common/assurance/formal_delivery_gates.spl:127; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/sha512.spl:517
```
- Review rationale: Read all twelve reported failures and the seed caveat. Target formal_delivery_gates still contains trailing-or conditions at 127, while sha512_text now delegates to sha512_bytes and the reported padded index assignment is absent. These mixed changes prevent adopting the report's claim that all source failures are immutable. Remaining bounded work: map the other ten current specs to owners and inspect parser continuation and crypto implementation history; no aggregate current verdict is supported.
- Review corrections: Historical valid label changed to uncertain for current aggregate; first-pass unexamined status remains needs_more_evidence. Current SHA-512 owner no longer matches reported line.

## u64_collections_clobber_recurrence_engine_2026-08-11 — the collections.rs stale-snapshot clobber is one commit replayed six times and still armed

- Source receipt: `adjudication_v2_29`; inspection `report_reviewed`; validity `valid`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:NONE; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-seed-builds-push.shs:283
```
- Review rationale: Read complete report including same-day retraction, all six incident ranges, complementary guard measurements, and source-clone hygiene instructions. The original recurrence remains valid, but the report expressly retracts armed recurrence in the shared clone. Target-bound guard search shows substantially expanded seed guard implementation; neither historical receipts nor source presence establishes current external originating-clone cleanup or hook enforcement. Next evidence must be owner-provided originating-clone status and enforcement receipt, not a redundant line-count guard.
- Review corrections: Keep historical validity; first-pass unexamined residual remains needs_more_evidence because external clone state is unavailable.

## undeclared_imported_symbols_census — Imported symbols declared nowhere in repo are silently accepted instead of erroring

- Source receipt: `adjudication_v2_29`; inspection `report_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:NONE; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/dashboard/dashboard_collectors.spl:8; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:518
```
- Review rationale: Independently read census scope, bucket definitions, deployment corrections, sample limits and ending caveat, plus checked dashboard imports still referencing the named cluster. The report's own missing ephemeral instrument and twin-tree corrections prevent promoting 1,226 historical entries into a current per-name provider ledger. Current aggregate remains uncertain; recover/rebuild the instrument and verify exact per-name providers and intentional negative fixtures before accepting population or closure. Middle appendices were not fully adjudicated.
- Review corrections: Keep needs_more_evidence; neither dashboard spot-check nor source warning implementation validates historical aggregate.

## unregistered_extern_backlog_enumeration_2026-08-01 — Externs declared in .spl are absent from the extern registry, so lanes silently drop them

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-extern-registration.shs; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-extern-registration.shs:85
```
- Review rationale: Read the full enumeration report and independently inspected extractor code: it recognizes decorator and bare/pub extern fn forms, skips comment lines and records explicit bare ABI separately. The 2,377-site increase is therefore a historical measurement expansion, not newly introduced debt. Current backing providers for the 1,308 symbols have not been verified; same-name twins in unrelated modules and directory-based bare exemptions are insufficient. Need a retained current declaration-to-provider ledger before accepting aggregate status.
- Review corrections: Upgrade inspection to source_reviewed for actual extractor, but keep unaccepted provider population and uncertain classification.

## vacuous_spec_corpus_census_and_inert_assertion_forms_2026-08-02 — 5,095 spec files contain inert assertion forms that pass without exercising anything

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:NONE; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/node_exec.rs:368
```
- Review rationale: Read the census model, positive/negative assertion-form probes, measured false positives, twin-tree handling and backlog caveat. Independently inspected current Node::Assert: it now evaluates condition and returns assert_stmt_failure when false, directly superseding one alleged inert form. Historical sample VHDL matchers cannot establish the 5,095-file population, and full ledger/current checker controls were not adjudicated. Need current representative failing controls plus per-file review before accepting corpus totals; no blanket deletion is justified.
- Review corrections: First-pass investigated/valid aggregate not accepted. Current bare-assert executor contradicts carrying old form classification forward; use uncertain and needs_more_evidence.

## verification_layer_orphans_and_dangling_refs_2026-08-02 — Guard scripts under scripts/check are unreachable from any root (orphaned) and refs dangle

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; validity `uncertain`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:NONE; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-guard-wiring.shs:157; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-guard-wiring.shs:205; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-dangling-references.shs:345
```
- Review rationale: Read report's original governance model and later false-positive/false-negative corrections. Current wiring code includes workflow/hook roots, retains helper nodes while excluding them as judged gates, and filters dead manifest dispatcher arms. Dangling checker now limits field-like definitions to type bodies and recognizes extern/abstract types. Thus historic 7/360/188 counts cannot stand as current reachability. Exact BFS, individual opt-out reasons and remaining names were not audited; need that retained current ledger before accepting aggregate, deletion or closure.
- Review corrections: Do not accept first-pass investigated aggregate from samples. Current checker model has further changes beyond report; residual population needs evidence.

## wm_action_applier_window_surface_session_and_web_window_request_2026-08-10 — wm_action_applier_spec: 2 of 17 examples RED — window-surface session and

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; validity `valid`; reproducibility `untested`.
- Solution `unknown`; structural change `unknown`; action `keep_open`; state `needs_more_evidence`.
- Evidence refs (verbatim source field; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_action_applier_window_surface_session_and_web_window_request_2026-08-10.md#L1-L75; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/wm_action_applier.spl#L56-L72; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/compositor.spl#L237-L260; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/compositor/wm_action_applier_spec.spl#L80-L110; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/compositor.spl:495-535,1081-1110
```
- Review rationale: Historical report and current spec require WindowSurface.session plus wm_action_web_window_request, and current owner lacks that field/helper. However current compositor deliberately stores GUI trees/focus in a content-handle registry, with create_windows_from_shared_scene/update_window_tree routing through that design; field absence alone no longer proves missing session behavior. Web action stores body HTML/identity without the asserted request surface. Preserve historical validity but conflicting current API/test authority needs investigation: trace registry observables and adopted design before adding a field or changing specs.
- Review corrections: Reject no-structural-change assertion and simplistic add-session remedy. Current deliberate registry ownership conflicts with old direct-field contract; stale closed heading also cannot establish resolution. All source reads independently bound to full c0 target; historical execution is not current reproduction.
