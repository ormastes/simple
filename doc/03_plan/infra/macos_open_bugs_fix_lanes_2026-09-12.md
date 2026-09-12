# macOS Open Bugs — Fix Lanes (2026-09-12)

Scope: every OPEN macOS-only bug in `doc/08_tracking/bug/*.md` + `bug_db.sdn` +
1 TODO in `doc/TODO.md`, as of `origin/main@808cf9c9826` (checked against PRs
merged today, #578-#581 — none overlap these items: #578/#581 are bugdb
triage/MSVC-link, #580 is engine2d font-race, all non-macOS-specific).

## Item table

| id | title (short) | file:line | area | fixable here (mac M4, Vulkan seed) | size | oracle |
|---|---|---|---|---|---|---|
| c_runtime_compiles_guard_red_on_macos_aarch64 | c-runtime push gate RED on mac | scripts/check/check-c-runtime-compiles-push.shs | runtime C | yes | S | `sh scripts/check/check-c-runtime-compiles-push.shs` PASS |
| bootstrap_macos_blocked_seed_compile_linux_only_stage3 | remaining `/proc` coupling in Stage-3 authority path | scripts/bootstrap/*, src/compiler_rust (stage3 authority lib) | Rust seed / scripts.shs | partial (no board, but /proc dep is host-generic) | M | Stage 2/3 admission on mac exits without `/proc` ENOENT |
| darwin_stage_binaries_clobber_bare_paths | tracked bare stage paths still wrong post-deploy | scripts/bootstrap/phase*, bootstrap/stage*/simple (tracked artifacts) | scripts.shs / deploy | yes | S | `git ls-tree` shows correct Mach-O per-triple paths, no bare clobber |
| macos_bootstrap_lane_platform_defect_cluster | lane not green through Stage 2 (8 sub-fixes landed) | scripts/bootstrap/**, needs fresh Stage-2 run | scripts.shs | yes (this host) | M | full Stage 1→2 run exits 0 |
| macos_full_cli_gui_admission_process_proof | Swift/ES builder self-test + live ES evidence blocked (exit 125) | scripts/check/build-macos-es-history-collector.shs | scripts.shs | partial (ES evidence needs TCC/root, self-test doesn't) | M | builder self-test PASS; live ES evidence documented as blocked-by-entitlement if still so |
| macos_gui_run_sigpipe_141_and_stale_winit_marker_gate | `macos-gui-run.shs` exits 141 after launch; winit-marker gate rejects dlopen route | scripts/gui/macos-gui-run.shs | scripts.shs | yes | S | script exits 0 after real GUI launch |
| macos_native_lane_freetype_missing_rust_bootstrap_multiplatform | CI never installs freetype for `Native — macOS aarch64` | .github/workflows/rust-bootstrap-multiplatform.yml | CI yaml | yes (edit only, CI run needed to confirm) | S | workflow run green |
| macos_stage4_deploy_test_tree_divergence_stepover | pre-existing test-tree divergence step-over recorded | scripts/check/check-test-tree-divergence*.shs, offender list doc | scripts.shs / docs | yes | S | delta guard PASS with recorded offender list |
| macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot | test runner blocked by inline-`unsafe` parse + wrong deploy slot | src/app/test_runner_new/*, bin/release deploy slot script | pure-Simple lib / scripts.shs | yes | M | `simple test` runs past the blocking parse on mac |
| macos_vulkan_2d_vector_font_empty_batch_native_fault | Vulkan 2D vector-font path faults natively on empty draw batch | src/os/compositor/host_compositor_core.spl | pure-Simple lib | yes (Vulkan present) | S | empty-batch fixture no longer faults |
| main_test_runnable_unsatisfiable_on_macos | no deployed binary has both `test` + reads-tree on mac | scripts/check/check-push-must-pass.shs (gate def) | scripts.shs | yes | M | gate finds a runnable binary or is scoped OPEN correctly |
| push_gates_unrunnable_on_macos_bsd_awk | 2 BSD-awk incompatibilities break push gates | scripts/check/*.shs (awk usages) | scripts.shs | yes | S | affected guards run clean under BSD awk |
| spipe_docgen_deployed_macos_cli_stale | deployed macOS CLI can't regen rendering knowledge manual | scripts docgen entrypoint (spipe) | scripts.shs / docs | blocked on admitted pure-Simple CLI (not purely local) | M | docgen runs on redeployed CLI |
| store_open_acid_gate_unrunnable_on_macos_aarch64 | ACID gate can't run on mac aarch64; recorded blocker wrong | scripts/check/check-store-open-acid.shs | scripts.shs | yes | S | gate runs, correct blocker documented or fixed |
| test_runner_ulimit_caps_unusable_on_macos | ulimit caps make `simple test <dir>` unusable | src/app/test_runner_new/* (ulimit wiring) | pure-Simple lib | yes | S | `simple test <dir>` runs under mac ulimits |
| vulkan_2d_c_compare_skips_on_macos | `check-vulkan-2d-c-compare.shs` always `skipped`, 2 causes | scripts/check/check-vulkan-2d-c-compare.shs | scripts.shs | yes (Vulkan + Chrome present) | S | compare runs to PASS/FAIL, not skip |
| gui_winit_window_not_registered_window_server | winit window composites but no Aqua activation; clicks/drags never land | scripts/gui/macos-gui-run.shs | scripts.shs | yes | M | click/drag lands in the live window |
| wm_metal_glass_multi_receipt_opacity | source fixed, runtime evidence unverified on Metal | doc-only evidence gap | docs | yes (Metal via xcrun works here) | S | capture real Metal receipt, update doc |
| TODO#23 sosix macOS provider | add macOS provider for sosix file driver | src/lib/nogc_async_mut/sosix/file_driver.spl:16 | pure-Simple lib | yes | M | provider implemented + spec passes on mac |

Total: 18 open macOS-scoped bugs, 1 open macOS TODO. (Excluded as CLOSED/CLOSED-STALE/RESOLVED/FIXED: interp_option_struct_semantics_macos_parity, macos_bootstrap_copy_mem_provider_gap, macos_stage4_full_cli_low_memory_runaway, macos_vulkan_host_wm_live_evidence_cpu_mirror_and_input_gap, macos_vulkan_native_entry_blockers, macos_vulkan_provider_availability_live, macos_seed_unbuildable_metal_module_ungated, macos_seed_unbuildable_metal_cfg, macos_winit_window_not_displayed, gui_smf_dynlib_hot_call_runtime_missing, bootstrap_stage1_native_build_llvm_icmp_segfault.)

## Fix lanes (disjoint files, ≤1 agent-day each, impact order)

**Lane 1 — Bootstrap lane crash/blocker chain (highest impact: blocks every mac bootstrap).**
Files: `scripts/bootstrap/**` (phase scripts), `bootstrap/stage1/simple`..`stage3/*` tracked artifacts, `scripts/check/check-bootstrap-preflight.shs`.
Items: macos_bootstrap_lane_platform_defect_cluster, bootstrap_macos_blocked_seed_compile_linux_only_stage3, darwin_stage_binaries_clobber_bare_paths.
Oracle: full Stage 1→2 (→3 if reachable) run exits 0, `git ls-tree` shows correct per-triple Mach-O paths.
Verify: `sh scripts/bootstrap/bootstrap-from-scratch.sh` (stage-limited) on this host.

**Lane 2 — C runtime + push-gate portability (blocks all pushes from mac).**
Files: `src/runtime/*.c` (non-vendor), `scripts/check/check-c-runtime-compiles-push.shs`, `scripts/check/*.shs` (BSD-awk sites), `scripts/check/check-store-open-acid.shs`, `scripts/check/check-push-must-pass.shs`.
Items: c_runtime_compiles_guard_red_on_macos_aarch64, push_gates_unrunnable_on_macos_bsd_awk, store_open_acid_gate_unrunnable_on_macos_aarch64, main_test_runnable_unsatisfiable_on_macos.
Oracle: each guard prints `PASS — n checked` on mac.
Verify: run each `check-*.shs` directly.

**Lane 3 — Test runner on mac (wrong/blocked output).**
Files: `src/app/test_runner_new/**` (ulimit wiring, inline-unsafe parse, deploy-slot).
Items: test_runner_ulimit_caps_unusable_on_macos, macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot.
Oracle: `simple test <dir>` runs to completion on mac under normal ulimits.
Verify: `bin/simple test test/01_unit/...` sample dir.

**Lane 4 — GUI/Vulkan mac runtime faults.**
Files: `scripts/gui/macos-gui-run.shs`, `src/os/compositor/host_compositor_core.spl`, `scripts/check/check-vulkan-2d-c-compare.shs`.
Items: macos_gui_run_sigpipe_141_and_stale_winit_marker_gate, gui_winit_window_not_registered_window_server, macos_vulkan_2d_vector_font_empty_batch_native_fault, vulkan_2d_c_compare_skips_on_macos.
Oracle: GUI window launches, receives real click/drag; empty-batch fixture no longer faults; compare gate returns PASS/FAIL not skip.
Verify: `sh scripts/gui/macos-gui-run.shs`, `sh scripts/check/check-vulkan-2d-c-compare.shs`.

**Lane 5 — CI/admission/docgen (blocked gates, lower urgency).**
Files: `.github/workflows/rust-bootstrap-multiplatform.yml`, `scripts/check/check-test-tree-divergence*.shs`, `scripts/check/build-macos-es-history-collector.shs`, spipe docgen entrypoint.
Items: macos_native_lane_freetype_missing_rust_bootstrap_multiplatform, macos_stage4_deploy_test_tree_divergence_stepover, macos_full_cli_gui_admission_process_proof, spipe_docgen_deployed_macos_cli_stale.
Oracle: CI workflow green; divergence delta guard PASS with recorded offenders; ES builder self-test PASS; docgen regenerates manual.
Verify: `gh workflow run`, `sh scripts/check/check-test-tree-divergence-delta.shs`.

**Lane 6 — Evidence/docs + sosix TODO (lowest urgency, no crash/gate impact).**
Files: `doc/08_tracking/bug/wm_metal_glass_multi_receipt_opacity_2026-07-27.md`, `src/lib/nogc_async_mut/sosix/file_driver.spl`.
Items: wm_metal_glass_multi_receipt_opacity (capture real Metal receipt via `xcrun metal`), TODO#23 sosix macOS provider.
Oracle: doc updated with real Metal capture; sosix macOS provider spec passes.
Verify: `bin/simple test` on the sosix file_driver spec.

## Unclassified
None — all 18 bugs + 1 todo assigned above.
