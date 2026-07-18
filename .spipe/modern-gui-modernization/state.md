# Feature: modern-gui-modernization

## Raw Request
complete next with spipe dev skill,  make modern gui...   doc/03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md

## Task Type
feature

## Refined Goal
Create and advance the next concrete SPipe lane for the modern GUI modernization plan so the repository has a dated modernization plan, testable acceptance criteria, and an executable next-step path toward a modern GUI.

## Acceptance Criteria
- AC-1: `doc/03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md` exists and identifies the next implementation slice with explicit scope, dependencies, evidence, and stop conditions.
- AC-2: The dated plan references existing UI modernization, Simple WM modernization, and generated/spec evidence artifacts instead of replacing or contradicting them.
- AC-3: The next slice has pass/fail verification commands that can be run once per session without requiring broad full-suite loops.
- AC-4: If the next slice changes UI workflow, evidence wrappers, generated manuals, or verification contracts, matching process documentation under `doc/07_guide`, `doc/06_spec`, `.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, or `.gemini/commands` is updated or explicitly marked not applicable.
- AC-5: Unrelated dirty worktree files remain untouched by this lane unless they are required by the modernization plan.

## Scope Exclusions
This SPipe dev pass does not claim full GUI modernization completion, cross-platform RenderDoc parity, or release readiness.

## Cooperative Review
N/A: this pass is a narrow planning and next-slice activation lane; no sidecar lanes are needed until implementation touches renderer, WM, browser, or evidence contracts.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: feature)
- plan: Added dated modernization plan at `doc/03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md`.
- implement: Added Web WM modern shell evidence wrapper, integration SSpec, mirrored manual, and guide page.
- verify: `sh -n scripts/check/check-web-wm-modern-shell-evidence.shs` passed.
- verify: `sh scripts/check/check-web-wm-modern-shell-evidence.shs` wrote explicit `environment-unavailable` evidence because `bin/simple` is absent and `bin/simple_native --version` exits 139 in this checkout.
- implement: Added PNG output support to `tools/electron-live-bitmap/capture_html_argb.js` so the evidence wrapper can emit the planned ARGB JSON plus PNG artifact pair.
- verify: `node --check tools/electron-live-bitmap/capture_html_argb.js` passed.
- blocker: Recorded `doc/08_tracking/bug/simple_runtime_unavailable_for_modern_gui_evidence_2026-06-26.md`; current runtime candidates are `bin/simple:missing`, `bin/release/simple:127`, missing platform release binaries, and `bin/simple_native:139`.
- implement: Added `src/compiler_rust/target/release/simple` as a local runtime fallback in the evidence wrapper.
- implement: Fixed the modern preview overlap by moving the preview-only quality inspector below the command palette, added a pinned/action-feedback desktop widget witness, and updated quality-contract detection for current runtime source.
- refactor: Cached `wm_theme_quality_summary("glass_dark")` once in the unit spec to avoid repeated expensive generator calls.
- verify: `src/compiler_rust/target/release/simple check test/01_unit/app/ui/web_wm_modern_shell_spec.spl` passed.
- verify: `src/compiler_rust/target/release/simple test test/01_unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter` passed: 5 passed, 0 failed.
- verify: `src/compiler_rust/target/release/simple test test/02_integration/app/ui/web_wm_modern_shell_evidence_spec.spl --mode=interpreter --clean` passed: 1 passed, 0 failed.
- verify: `sh scripts/check/check-web-wm-modern-shell-evidence.shs` passed with `web_wm_modern_shell_evidence_status=pass`, nonblank ARGB/PNG artifacts, `audit_pass=pass`, zero unexpected overlaps, zero clipping, zero contrast failures, and zero touch failures.
- implement: Added Electron interaction evidence at `tools/electron-live-bitmap/interact_html_controls.js` and wired it into `scripts/check/check-web-wm-modern-shell-evidence.shs`.
- verify: The wrapper now records `simple_wm_modern_preview_interaction.json` and `simple_wm_modern_preview_after_interaction.png`; final pass included focus, keyboard/input, pointer, and click delivery with `web_wm_modern_shell_evidence_interaction_event_count=13`.
- verify: `src/compiler_rust/target/release/simple spipe-docgen test/02_integration/app/ui/web_wm_modern_shell_evidence_spec.spl --output doc/06_spec --no-index` completed with 0 stubs.
- verify: `sh scripts/audit/direct-env-runtime-guard.shs --working` passed and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
