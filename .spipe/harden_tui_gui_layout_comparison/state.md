# Feature: harden-tui-gui-layout-comparison

## Raw Request
$sp_dev harden tui and gui layout comparison and fix. and optimize size and perf with (metal, vulkan, cuda, simd cpu) also. research web and local and plan and design deeply.

## Task Type
feature

## Refined Goal
Create a verified plan and implementation path that hardens TUI/GUI layout comparison, fixes discovered comparison defects, and designs measurable size/performance optimization paths for Metal, Vulkan, CUDA, and SIMD CPU backends.

## Acceptance Criteria
- AC-1: Local research identifies the current TUI, GUI, layout, renderer, capture, and comparison code paths, existing tests, known bugs, and size/performance constraints.
- AC-2: Domain research records current external practices for visual/layout regression testing, UI diff tolerances, GPU backend performance, binary size control, and CPU SIMD optimization, with sources.
- AC-3: Requirement options and NFR options are written with pros, cons, and effort estimates, and final requirements are created only after user selection.
- AC-4: Architecture and detail design define a TUI/GUI layout comparison contract, failure triage model, fixture/capture strategy, tolerance rules, and cross-backend optimization plan for Metal, Vulkan, CUDA, and SIMD CPU.
- AC-5: SPipe system specs cover matching layouts, intentional mismatch reporting, capture reproducibility, and backend/performance evidence gates without placeholder assertions.
- AC-6: Implementation fixes discovered TUI/GUI layout comparison defects and preserves existing GUI/TUI behavior.
- AC-7: Verification includes relevant Simple checks/tests, generated scenario manuals, no executable specs under doc/06_spec, and evidence for size/performance targets or explicitly tracked follow-up bugs where hardware/runtime coverage is unavailable.

## Scope Exclusions
Shipping production GPU compute kernels for every backend is excluded unless selected requirements explicitly require it; the minimum scope is a designed and testable backend strategy with evidence gates and implemented fixes for currently reachable comparison defects.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
- research: Wrote local/domain research and feature/NFR option artifacts.
- research: Baseline focused tests show wm_compare emulated and TUI screen specs pass under `src/compiler_rust/target/debug/simple`, while `backend_screenshot_compare_spec.spl` fails from stale imports/API drift; `doc/06_spec` contains zero executable specs.
- implement: Removed stale backend screenshot comparison imports, rewrote the spec and matcher mirror around deterministic comparison buffers, and verified the focused backend screenshot, wm_compare emulated, and TUI screen specs pass.
- implement: Fixed screenshot comparison threshold semantics so `exact_match` means byte-for-byte equality and `passed` means within threshold; added focused assertions and reran backend screenshot, wm_compare emulated, and TUI screen specs successfully.
- implement: Replaced TUI parse-error placeholder assertions with diagnostic assertions and verified the TUI screen and backend screenshot comparison specs still pass.
- spec: Regenerated and manually improved `doc/06_spec/integration/rendering/backend_screenshot_compare_spec.md`; verified backend screenshot spec still passes and `doc/06_spec` contains zero executable specs.
- spec: Regenerated and manually improved `doc/06_spec/system/gui/tui_screen_spec.md`; verified the TUI screen spec still passes and `doc/06_spec` contains zero executable specs.
- research: Recorded CPU SIMD backend-session API drift as `doc/08_tracking/bug/backend_session_kind_cpu_simd_api_drift_2026-06-01.md` for the backend-qualified design lane.
- verify: Focused blocker audit found no live placeholder/TODO/stub markers in changed executable specs/source; backend screenshot, TUI screen, and wm_compare emulated specs pass; `doc/06_spec` executable spec count remains zero.
- perf: Reduced the wm_compare emulated capture shape-only fixture from 160x120 to 40x30 in the executable spec and matcher mirror; focused wm_compare spec duration dropped from about 58.7s to 7.9s while preserving the 3 passing scenarios.
- implement: Hardened wm_compare emulated capture against invalid viewport dimensions; failed captures now return diagnostic errors and exact comparison reports a non-exact result instead of treating two empty buffers as a match.
- spec: Updated `doc/06_spec/system/wm_compare/emulated_capture_spec.md` manually with the new invalid-viewport scenarios because automatic docgen is currently blocked by unrelated `flat_ast_bridge_part2.spl` parse state in the dirty worktree.
- verify: wm_compare emulated spec now passes 5 scenarios; backend screenshot and TUI focused specs still pass; `doc/06_spec` executable spec count remains zero and changed executable artifacts have no placeholder/TODO blockers.
- implement: Hardened shared `compare_exact` so invalid dimensions are non-exact with zero match percentage and max-channel diagnostic drift; added wm_compare HTML compatibility coverage.
- verify: `html_compat_spec` now passes 14 scenarios; wm_compare emulated, backend screenshot, and TUI focused specs still pass; doc layout and placeholder gates remain clean.
- verify: Rechecked CPU SIMD backend-session drift with clean backend-session and CPU SIMD session specs plus direct checks of the GC/no-GC session files; the original `BackendSessionKind.CpuSimd` field error is not currently reproducible, so the bug record is updated as monitored.
- implement: Hardened backend runtime evidence summary so Metal and Vulkan participate in selected-runtime probing before CUDA/compute fallbacks, and the summary now exposes explicit Metal, Vulkan, CUDA, and CPU SIMD architecture status fields.
- verify: `backend_probe_strict_spec` passes 8 scenarios uncached; backend-session, CPU SIMD session, and wm_compare HTML compatibility specs pass; doc layout and placeholder gates remain clean.
- spec: Reviewed and improved `doc/06_spec/unit/lib/gpu/engine2d/backend_probe_strict_spec.md` with a manual-purpose section explaining the strict backend evidence contract for Metal, Vulkan, CUDA, WebGPU, OpenCL, ROCm, OptiX, and CPU SIMD lanes.
- verify: Re-ran `backend_probe_strict_spec` uncached after manual review; 8 scenarios pass, `doc/06_spec` executable count is zero, and backend probe source/spec/manual placeholder scan is clean.
- implement: Hardened shared wm_compare `compare_exact` so equal-length but truncated buffers cannot be reported as exact; the comparator now requires both buffers to match the expected viewport pixel count.
- verify: `html_compat_spec` now passes 15 scenarios uncached; wm_compare emulated, backend screenshot comparison, and backend probe strict specs pass uncached; doc layout and placeholder gates remain clean.
- implement: Hardened compositor `compare_pixel_buffers` so zero or negative viewport dimensions are failed comparisons instead of exact empty-buffer matches.
- spec: Added backend screenshot comparison coverage and manual text for invalid-dimension failures.
- verify: Backend screenshot comparison now passes 7 scenarios uncached; wm_compare HTML compatibility, wm_compare emulated capture, and backend probe strict specs pass uncached; doc layout and placeholder gates remain clean.
- implement: Hardened compositor `generate_diff_image` so truncated buffers still produce viewport-sized diagnostics and mark missing pixels as red differences.
- spec: Added backend screenshot comparison coverage and manual text for truncated-buffer diff diagnostics.
- verify: Backend screenshot comparison now passes 8 scenarios uncached; wm_compare HTML compatibility, wm_compare emulated capture, and backend probe strict specs pass uncached; doc layout and placeholder gates remain clean.
- spec: Added backend screenshot comparison coverage proving invalid dimensions remain failed through `compare_with_profile`, which is the path used by WM consistency callers.
- verify: Backend screenshot comparison now passes 9 scenarios uncached; wm_compare HTML compatibility, wm_compare emulated capture, and backend probe strict specs pass uncached; doc layout and placeholder gates remain clean.
- implement: Hardened wm_compare `compare_perceptual` so invalid dimensions or incomplete/truncated buffers report `0` perceptual match instead of scoring only the available prefix.
- verify: `html_compat_spec` now passes 16 scenarios uncached; backend screenshot comparison, wm_compare emulated capture, and backend probe strict specs pass uncached; doc layout and placeholder gates remain clean.
- spec: Synced ignored SPipe matcher mirror `test/sys/wm_compare/.spipe_matchers_html_compat_spec.spl` with the invalid-dimension, truncated exact, and truncated perceptual wm_compare comparison cases.
- verify: The executable HTML compatibility spec still passes 16 scenarios uncached; the ignored matcher mirror passes direct `simple check`; backend screenshot comparison and backend probe strict specs pass uncached; doc layout and placeholder gates remain clean.
- implement: Hardened wm_compare `compare_pair` so capture viewport metadata mismatches are treated as capture failures before exact pixel acceptance.
- spec: Added HTML compatibility coverage and manual text for mismatched capture viewport metadata.
- verify: `html_compat_spec` now passes 17 scenarios uncached; backend screenshot comparison, wm_compare emulated capture, and backend probe strict specs pass uncached; doc layout and placeholder gates remain clean.
- spec: Synced ignored SPipe matcher mirror `test/sys/wm_compare/.spipe_matchers_html_compat_spec.spl` with the viewport metadata mismatch pair-level scenario.
- verify: The matcher mirror passes direct `simple check`; HTML compatibility, backend screenshot comparison, and backend probe strict specs pass uncached; doc layout and placeholder gates remain clean.
- implement: Hardened famous-site corpus `compare_site_sample` so Chrome/Simple capture viewport metadata mismatches are treated as capture failures before exact pixel acceptance.
- spec: Added focused `site_corpus_pair_spec` and generated/improved its manual for the corpus pair metadata contract.
- verify: `site_corpus_pair_spec`, `html_compat_spec`, `backend_screenshot_compare_spec`, and `backend_probe_strict_spec` pass uncached; doc layout and placeholder gates remain clean.
- spec: Restored the manual-purpose section in `doc/06_spec/system/wm_compare/site_corpus_pair_spec.md` after doc generation and reverified the site corpus pair spec plus doc layout/placeholder gates.
- design: Added preselection architecture, detail design, system-test plan, and agent-task docs for the option-independent comparison/backend evidence contract while leaving final requirements/design selection pending user choice.
- verify: Re-ran focused site corpus pair, HTML compatibility, emulated capture, backend screenshot comparison, and backend probe strict specs; all pass, `doc/06_spec` executable spec count is zero, and changed executable artifacts have no placeholder/TODO blockers.
- requirements: Treated user "go" as approval of the previously recommended Feature Option 3 and NFR Option C; wrote final feature/NFR requirements and removed the option files per workflow.
- design: Promoted architecture, detail design, system-test plan, and agent tasks from preselection draft to selected 3/C scope, including structural layout and backend-qualified measurement completion items.
- verify: Requirement option files are removed, `doc/06_spec` executable spec count is zero, backend probe strict passes 8 scenarios, HTML compatibility passes 17, backend screenshot comparison passes 9, and site corpus pair passes 1.
