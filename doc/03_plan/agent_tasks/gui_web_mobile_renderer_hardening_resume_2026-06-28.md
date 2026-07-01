# GUI/Web/Mobile Renderer Hardening Resume Plan

## Recovered Objective

Resume the SPipe-driven hardening lane for Simple GUI and web rendering across
Chrome, Electron, Tauri2 iOS/WKWebView/Metal, and Tauri2 Android/WebView/Vulkan.
The lane must improve event handling evidence, rendering capture evidence,
performance evidence, animation evidence, coverage, system tests, docs, skills,
and GitHub synchronization without making false parity claims.

## Authoritative Workspace State

- Current workspace: `/Users/ormastes/simple`.
- Current branch at original recovery: `codex/tauri-mobile-renderer-parity-2026-06-26`.
- Current branch head at original recovery:
  `ad151553c2 feat: add tauri mobile renderer parity evidence`.
- Current branch upstream at original recovery:
  `origin/codex/tauri-mobile-renderer-parity-2026-06-26`.
- Branch/upstream status at original recovery: `0 ahead, 0 behind`.
- `origin/main` has later crash-lane commits, including:
  - `810824dab0 test(gui): surface mobile interaction proof in parity report`
  - `6acc8b06b5 test(gui): surface metal render proof in report`
  - `7a1dc64ccd test(gui): report electron live smoke proof`
  - `ab7929448f test(rendering): surface electron gpu crash diagnostics`
- The old temp worktree `/tmp/simple-mobile-hardening` no longer exists.
- The current workspace is dirty. Treat existing dirty files as in-flight work;
  do not reset, overwrite, or fold them into unrelated cleanup without an
  explicit ownership decision.

## Post-Sync Audit (2026-07-01)

- Current branch is still `codex/tauri-mobile-renderer-parity-2026-06-26`.
- Current checked-out head is
  `4d4f6162ab44f92206778195a3388e264917711c`
  (`test(gui): harden mobile renderer evidence reporting`).
- Current upstream is
  `origin/codex/tauri-mobile-renderer-parity-2026-06-26`; local and upstream
  are `0 ahead, 0 behind`, and `git ls-remote` during sync verified the remote
  bookmark at the same commit.
- The branch is not integrated with `origin/main`: the four crash-lane commits
  listed above are not ancestors of `HEAD`, and
  `git log --cherry-pick --right-only HEAD...origin/main` still lists those
  commits plus many later renderer-evidence hardening commits.
- Current branch content does expose the same named evidence surfaces for the
  four listed crash-lane topics:
  mobile interaction latency rows in
  `check-tauri-mobile-renderer-parity-evidence.shs`, production Metal render-log
  gate rows in `check-tauri-mobile-renderer-parity-evidence.shs` and
  `check-macos-metal-render-log-compare.shs`, Electron live-smoke proof rows in
  `check-electron-live-smoke.shs`, and Electron RenderDoc/GPU crash diagnostic
  rows in the RenderDoc aggregate wrappers. This is not a substitute for full
  `origin/main` reconciliation because the patches are not patch-equivalent and
  later main hardening remains unapplied.
- The earlier sync attempt saw `.git/index.lock` with no `lsof` holder observed.
  Recheck ownership and active processes before any jj commit/rebase/push from
  this plan.
- The worktree is broadly dirty across SPipe state, docs, scripts, source,
  generated manuals, deleted build artifacts, and untracked oversized vendor
  files. Treat this as mixed other-agent work until the intended commit scope is
  explicitly isolated.

Current reconciliation decision: do not mark this resume plan complete. The
feature branch is synced to its own GitHub ref, but it is still intentionally
separate from `origin/main` and the remaining main renderer hardening commits.
The next safe action is a scoped port/rebase plan in a clean or isolated
worktree, not a broad commit of the current dirty checkout.

`jj status` became readable again after the stale `.git/index.lock` disappeared,
but it still refuses to snapshot oversized untracked Windows vendor libraries
under `src/compiler_rust/vendor/**`. Treat jj as inspection-only in this checkout
until those vendor files are ignored, removed from the dirty set by their owner,
or deliberately included with an explicit snapshot-size decision.

## Mac GUI/Metal Hardening Checklist

The mac GUI/Metal slice is complete only when all rows below are proven from
current artifacts, not from stale reports or branch-memory:

1. Production GUI/Web source evidence:
   - Run or consume
     `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`.
   - Required rows:
     `production_gui_web_renderer_parity_status=pass`,
     `production_gui_web_renderer_parity_backend_status=pass`,
     `production_gui_web_renderer_parity_backend_exact=true`,
     `production_gui_web_renderer_parity_backend_same_frame_readback=true`,
     `production_gui_web_renderer_parity_backend_blur_or_tolerance_used=false`,
     and `production_gui_web_renderer_parity_metal_readback_status=pass`.
   - Linux or non-Darwin Metal rows may be typed unavailable, but they are not a
     macOS Metal pass.

2. macOS Metal render-log comparison:
   - Run or consume `scripts/check/check-macos-metal-render-log-compare.shs`
     with current input envs for generated Metal readback, Engine2D framebuffer
     readback, and browser Metal backing.
   - Required rows:
     `macos_metal_render_log_compare_status=pass`,
     `macos_metal_render_log_compare_required_api=metal`,
     `macos_metal_render_log_compare_generated_readback_gate_status=pass`,
     `macos_metal_render_log_compare_framebuffer_readback_gate_status=pass`,
     `macos_metal_render_log_compare_browser_backing_gate_status=pass`,
     `macos_metal_render_log_compare_pairwise_gate_status=pass`,
     `macos_metal_render_log_compare_argb_source_gate_status=pass`,
     and `macos_metal_render_log_compare_blocked_gate_count=0`.
   - Required pairwise rows:
     `macos_metal_render_log_compare_electron_chrome_pairwise_diff_status=pass`,
     `macos_metal_render_log_compare_electron_simple_pairwise_diff_status=pass`,
     and `macos_metal_render_log_compare_chrome_simple_pairwise_diff_status=pass`.

3. Browser-backed Metal identity:
   - Electron and Chrome rows must prove Metal-backed browser rendering through
     their backing metadata, not only nonblank bitmaps.
   - Required rows include
     `macos_metal_render_log_compare_electron_browser_backing_status=pass`,
     `macos_metal_render_log_compare_chrome_browser_backing_status=pass`,
     and nonempty backing-source file/artifact status rows.
   - An ANGLE/Vulkan/SwiftShader fallback, missing backing source, duplicated
     source, symlink, hardlink, or nonregular artifact is a failed or blocked
     Metal proof.

4. Simple, Chrome, and Electron ARGB evidence:
   - Simple, Chrome, and Electron ARGB artifacts must be regular nonempty files
     with matching viewport, matching checksums, nonblank pixels, and exact
     pairwise diffs.
   - The generated `simple.srl.env`, `chrome.srl.env`, `electron.srl.env`, and
     `compare.srl.env` render logs must be archived with the evidence report.

5. Optional GPU capture:
   - If `MACOS_METAL_RENDER_LOG_REQUIRE_GPU_CAPTURE=1`, the Xcode GPU capture
     gate must pass and the capture artifact must have the expected magic.
   - If the variable is not set, `not-required` is acceptable only for the GPU
     capture gate; it does not weaken the raw Metal readback, browser backing,
     or ARGB pairwise gates.

6. GitHub reconciliation:
   - This feature branch is synced to its own remote ref, but not to
     `origin/main`.
   - Before claiming "after sync gh" completion, either rebase/port the relevant
     `origin/main` renderer hardening commits into an isolated worktree, or
     record a commit-by-commit equivalence table that explains why each right-only
     renderer evidence commit is intentionally not applied.
   - Do not commit from the current checkout until the mixed dirty files and
     oversized untracked vendor libraries are scoped.

## Production GUI/Web Metal Aggregate Pass (2026-07-02)

Current scoped worktree:
`/tmp/simple-mac-metal-materialize` on
`codex/tauri-mobile-renderer-parity-2026-06-26`.

Current production aggregate evidence:
`build/goal-production-gui-web-parity-current/evidence.env`.

The aggregate was rerun with:

```sh
BUILD_ROOT=build/goal-production-gui-web-parity-current \
REPORT_PATH=build/goal-production-gui-web-parity-current/report-after-event.md \
SIMPLE_BIN=/Users/ormastes/simple/bin/simple \
PRODUCTION_GUI_WEB_RENDERER_PARITY_SUBCHECK_TIMEOUT_SECS=300 \
PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_MANIFEST_RESUME=1 \
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
```

Observed pass rows:

- `production_gui_web_renderer_parity_status=pass`
- `production_gui_web_renderer_parity_layout_manifest_status=pass`
- `layout_electron_simple_web_layout_manifest_resumed_count=50`
- `layout_electron_simple_web_layout_manifest_rerun_count=0`
- `production_gui_web_renderer_parity_surface_manifest_status=pass`
- `production_gui_web_renderer_parity_backend_status=pass`
- `production_gui_web_renderer_parity_font_offload_status=pass`
- `production_gui_web_renderer_parity_font_offload_metal_payload_status=pass`
- `production_gui_web_renderer_parity_metal_readback_status=pass`
- `production_gui_web_renderer_parity_metal_render_log_status=pass`
- `production_gui_web_renderer_parity_metal_render_log_blocked_gate_count=0`
- `production_gui_web_renderer_parity_event_routing_status=pass`
- `production_gui_web_renderer_parity_event_routing_validation_status=pass`
- `production_gui_web_renderer_parity_event_routing_proof_source_artifact_status=pass`

Supporting hardening added in this slice:

- `check-electron-simple-web-layout-manifest-evidence.shs` now honors
  `ELECTRON_LAYOUT_MANIFEST_RESUME=1` and reuses only matching scene/viewport
  per-case evidence.
- `check-wm-browser-event-routing-evidence.shs` runs Electron natively on macOS
  instead of requiring Linux `xvfb-run`, and emits the validation,
  proof-source, timing, animation, browser identity, and version rows required
  by the production aggregate.

This completes the desktop/macOS production GUI/Web Metal aggregate gate for
the current scoped artifacts. The full persistent mobile renderer hardening goal
still requires current Tauri iOS/WKWebView Metal and Android/WebView Vulkan
evidence from `check-tauri-mobile-renderer-parity-evidence.shs` before the
overall lane can be marked complete.

## Renderer Commit Reconciliation Snapshot

This snapshot covers only renderer evidence commits relevant to the mac
GUI/Metal, Electron/RenderDoc, and Tauri mobile parity plan. It is not a full
`origin/main` merge audit.

| origin/main commit | Topic | Current branch status | Evidence in this branch |
| --- | --- | --- | --- |
| `810824dab0` | Surface mobile interaction proof in Tauri parity report | Represented by current branch rows, not patch-equivalent | `check-tauri-mobile-renderer-parity-evidence.shs` reports `*_mdi_interaction_latency_status` and MDI event/capture/perf/animation detail; `tauri_mobile_renderer_parity_evidence_spec.spl` asserts iOS/Android interaction latency rows. |
| `6acc8b06b5` | Surface Metal render proof in macOS render-log report | Represented by current branch rows, not patch-equivalent | `check-macos-metal-render-log-compare.shs` emits Metal render-log compare status, required API, pairwise statuses, generated Simple/Chrome/Electron `.srl.env` logs, and report rows. |
| `7a1dc64ccd` | Report Electron live-smoke proof | Represented by current branch rows, not patch-equivalent | `check-electron-live-smoke.shs` emits proof source, Electron/Chrome process versions, screenshot dimensions/checksum/nontransparent/colors, event dispatch, performance, animation, and no-blur policy rows; the validator spec references those fields. |
| `ab7929448f` | Surface Electron GPU crash diagnostics for RenderDoc | Represented by current branch rows, not patch-equivalent | RenderDoc Electron gate and aggregate scripts/specs include GPU-process crash/fatal diagnostic handling and fail-closed missing `.rdc` behavior. |
| `fe6b145228` | Require production Metal render logs before mobile parity pass | Represented by current branch rows, not patch-equivalent | `check-tauri-mobile-renderer-parity-evidence.shs` consumes `production_gui_web_renderer_parity_metal_render_log_*` fields and carries them into mobile parity status decisions. |
| `e139a317ba` / `5f65fec42f` | Emit macOS Metal render-log file reasons and artifact status | Represented by current branch rows, not patch-equivalent | `check-macos-metal-render-log-compare.shs` emits env file status/reason/artifact rows for generated readback, framebuffer readback, browser backing, GPU capture, Simple/Chrome/Electron ARGB artifacts, and browser backing sources. |
| `7832d36c1f` | Forward macOS Metal blocked gates into aggregate coverage | Not proven in this branch-level audit | Current Metal compare script emits `macos_metal_render_log_compare_blocked_gate_count` and `blocked_gates`; the aggregate `gui_renderdoc_feature_coverage` path still needs isolated comparison against `origin/main` before claiming equivalent forwarding. |
| Later right-only renderer commits from `HEAD...origin/main` | Provenance hardening, symlink/hardlink/nonregular/duplicate rejection, stale evidence detection, current-artifact discovery, browser backing validation, mobile screenshot density, ARGB content validation, and seed-forbid fixes | Not reconciled | The current branch contains many equivalent-looking guards, but there are too many right-only commits to claim equivalence from spot checks. Use an isolated worktree for rebase/port or generate a full table before marking this plan complete. |

Current action decision: keep the feature branch synced to its own remote while
the mac GUI/Metal checklist and reconciliation table guide the next isolated
integration pass. Do not mark this plan done from this dirty checkout.

## Isolated Integration Work Order (2026-07-02)

Scoped command used for the work-order count:

```sh
git log --cherry-pick --right-only HEAD...origin/main -- \
  scripts/check/check-macos-metal-render-log-compare.shs \
  test/03_system/check/macos_metal_render_log_compare_spec.spl \
  scripts/check/check-production-gui-web-renderer-parity-evidence.shs \
  test/03_system/check/production_gui_web_renderer_parity_gate_spec.spl \
  scripts/check/check-tauri-mobile-renderer-parity-evidence.shs \
  test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl \
  scripts/check/check-electron-live-smoke.shs \
  test/03_system/check/electron_live_smoke_proof_validator_spec.spl \
  scripts/check/check-renderdoc-electron-html-gate.shs \
  scripts/check/check-gui-renderdoc-feature-coverage-status.shs \
  scripts/check/check-gui-widget-renderdoc-goal-status.shs \
  test/03_system/check/renderdoc_electron_html_gate_spec.spl \
  test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl \
  test/03_system/check/gui_widget_renderdoc_goal_status_spec.spl
```

Current scoped result: 396 right-only `origin/main` commits still touch these
renderer evidence files. Bucketed by subject from commit titles:

| Bucket | Count | Example right-only commits |
| --- | ---: | --- |
| macOS Metal render-log/readback | 45 | `7832d36c1f`, `6acc8b06b5` |
| Electron live smoke / Electron RenderDoc | 49 | `a0b05ca9dd`, `4b310257ad` |
| Tauri mobile iOS/Android renderer evidence | 65 | `810824dab0`, `5cede97315` |
| RenderDoc aggregate/widget/html gates | 37 | `b222c3b517`, `f093031da8` |
| Production GUI/Web parity and backend gates | 70 | `a18731ea11`, `36b544843c` |
| Provenance/artifact guards | 34 | `4f7986a712`, `d908c5e480` |
| Mixed or uncategorized renderer hardening | 96 | `0915c42175`, `fee4c9f75f` |

Next isolated pass:

1. Create a clean worktree from this branch head, not from the current dirty
   checkout.
2. Cherry-pick or rebase the 396 scoped commits in dependency order, stopping at
   the first semantic conflict.
3. For each resolved bucket, run only the matching focused specs once:
   `macos_metal_render_log_compare_spec.spl`,
   `production_gui_web_renderer_parity_gate_spec.spl`,
   `tauri_mobile_renderer_parity_evidence_spec.spl`,
   `electron_live_smoke_proof_validator_spec.spl`,
   `renderdoc_electron_html_gate_spec.spl`,
   `gui_renderdoc_feature_coverage_status_spec.spl`, and
   `gui_widget_renderdoc_goal_status_spec.spl`.
4. After all focused specs pass, run the mandatory layout and direct-env guards:
   `find doc/06_spec -name '*_spec.spl' | wc -l`,
   `sh scripts/audit/direct-env-runtime-guard.shs --working`, and
   `sh scripts/audit/direct-env-runtime-guard.shs --staged`.
5. Only then update this plan from "not reconciled" to either a passing port or
   a precise blocker with the first failing commit/spec.

This work order is intentionally not a completion claim. It makes the remaining
GitHub-sync delta executable without absorbing unrelated SimpleOS, FPGA, vendor,
or generated-artifact changes from the shared checkout.

### Integration Probe (2026-07-02)

Probe setup:

- Generated `/tmp/simple_renderer_scoped_origin_main.patch` from
  `git diff --binary HEAD...origin/main -- <scoped renderer files>`.
- Patch size: 1,366,482 bytes across 14 renderer evidence files.
- Created disposable clean worktree:
  `/tmp/simple-mac-metal-reconcile-probe` at
  `4d4f6162ab44f92206778195a3388e264917711c`.

Probe results:

- Plain `git apply --check` fails. Several files were independently added or
  substantially changed on this feature branch, so the raw patch sees existing
  target files or context mismatches.
- `git apply --3way --check` exits `0`, so Git can build a 3-way merge base for
  the scoped renderer delta, but it predicts manual conflicts.

Clean 3-way files:

- `scripts/check/check-electron-live-smoke.shs`
- `scripts/check/check-macos-metal-render-log-compare.shs`
- `scripts/check/check-renderdoc-electron-html-gate.shs`
- `scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`
- `test/03_system/check/gui_widget_renderdoc_goal_status_spec.spl`
- `test/03_system/check/production_gui_web_renderer_parity_gate_spec.spl`

Predicted manual-conflict files:

- `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`
- `scripts/check/check-gui-widget-renderdoc-goal-status.shs`
- `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`
- `test/03_system/check/electron_live_smoke_proof_validator_spec.spl`
- `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl`
- `test/03_system/check/macos_metal_render_log_compare_spec.spl`
- `test/03_system/check/renderdoc_electron_html_gate_spec.spl`
- `test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl`

Next integration action: in the disposable worktree, apply the 3-way patch and
resolve only the eight predicted conflict files, then run the focused specs
listed above once. Do not apply the patch in the shared checkout.

### Applied 3-Way Probe Conflict Triage (2026-07-02)

The 3-way patch was applied in `/tmp/simple-mac-metal-reconcile-probe` only.
It originally stopped with unresolved conflicts and left the main checkout
untouched. The disposable worktree conflict triage now has these results:

| File | Conflict blocks | First conflict line | Resolution priority |
| --- | ---: | ---: | --- |
| `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` | 0 | resolved | Resolved in disposable worktree: kept the richer `origin/main` aggregate surface and preserved this branch's top-level Electron GPU-process exit passthrough rows and report summary. `sh -n` passed and the file is staged in the disposable worktree. |
| `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl` | 0 | resolved | Resolved with the aggregate script: kept the expanded `origin/main` aggregate expectations and retained assertions for `electron_renderdoc_gate_gpu_process_exit_*` rows. `/Users/ormastes/simple/bin/simple check` passed and the file is staged in the disposable worktree. |
| `test/03_system/check/renderdoc_electron_html_gate_spec.spl` | 0 | resolved | Resolved in disposable worktree: kept the `origin/main` superset that preserves GPU-process crash diagnostics and adds launch metadata plus source-contract freshness checks. `/Users/ormastes/simple/bin/simple check` passed and the file is staged in the disposable worktree. |
| `test/03_system/check/electron_live_smoke_proof_validator_spec.spl` | 0 | resolved | Resolved in disposable worktree: kept the comprehensive `origin/main` validator coverage for complete live proof, proof-source/proof-JSON provenance, Chromium/Electron process versions, screenshot artifact integrity, event/perf/animation rows, strict numeric/boolean typing, and early wrapper diagnostics; updated metadata to this resume plan and requirement/design docs. `/Users/ormastes/simple/bin/simple check` passed and the file is staged in the disposable worktree. |
| `test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl` | 0 | resolved | Resolved in disposable worktree: kept the richer `origin/main` mobile evidence coverage, retained explicit MDI interaction-latency assertions, and restored production Metal render-log fixture rows plus forwarded `tauri_mobile_renderer_parity_production_metal_render_log_*` expectations. `/Users/ormastes/simple/bin/simple check` passed and the file is staged in the disposable worktree. |
| `scripts/check/check-gui-widget-renderdoc-goal-status.shs` | 0 | resolved | Resolved in disposable worktree: kept `origin/main` Electron launch exit/timeout/metadata rows in both env output and Markdown report. `sh -n` passed and the file is staged in the disposable worktree. |
| `test/03_system/check/macos_metal_render_log_compare_spec.spl` | 0 | resolved | Resolved in disposable worktree: kept the comprehensive controlled-fixture spec from `origin/main`, updated its metadata to this mac/mobile resume plan and requirement/design docs, and confirmed it still asserts gate summary, backing, pairwise ARGB, artifact, and Xcode capture report rows. `/Users/ormastes/simple/bin/simple check` passed and the file is staged in the disposable worktree. |
| `scripts/check/check-production-gui-web-renderer-parity-evidence.shs` | 0 | resolved | Resolved in disposable worktree: kept `origin/main` Simple binary provenance rows and preserved this branch's 300-second subcheck timeout default. `sh -n` passed and the file is staged in the disposable worktree. |

Cleanly patched files in the disposable worktree:

- `scripts/check/check-electron-live-smoke.shs`
- `scripts/check/check-macos-metal-render-log-compare.shs`
- `scripts/check/check-renderdoc-electron-html-gate.shs`
- `scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`
- `test/03_system/check/gui_widget_renderdoc_goal_status_spec.spl`
  (`/Users/ormastes/simple/bin/simple check` passed)
- `test/03_system/check/production_gui_web_renderer_parity_gate_spec.spl`
  (`/Users/ormastes/simple/bin/simple check` passed)

Remaining unresolved files in `/tmp/simple-mac-metal-reconcile-probe`: 0.

Aggregate merge result: the resolved aggregate keeps the `origin/main` evidence
surface, including browser-backing source/provenance rows, Electron launch
metadata, ARGB artifact file/status rows, GUI showcase 4K/8K perf rows, and
macOS Metal blocked-gate forwarding. It also preserves this branch's top-level
Electron GPU-process crash diagnostics:
`electron_renderdoc_gate_gpu_process_exit_status`,
`electron_renderdoc_gate_gpu_process_exit_count`,
`electron_renderdoc_gate_gpu_process_exit_codes`, and
`electron_renderdoc_gate_gpu_process_exit_reason`, sourced from the
`rdoc_electron_html_gate_gpu_process_exit_*` rows emitted by
`check-renderdoc-electron-html-gate.shs`. The already-present
`gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_*` rows remain covered
by the aggregate spec.

Focused probe checks passed:

- `sh -n` for the touched shell wrappers:
  `check-gui-renderdoc-feature-coverage-status.shs`,
  `check-gui-widget-renderdoc-goal-status.shs`,
  `check-production-gui-web-renderer-parity-evidence.shs`,
  `check-renderdoc-electron-html-gate.shs`,
  `check-tauri-mobile-renderer-parity-evidence.shs`,
  `check-electron-live-smoke.shs`, and
  `check-macos-metal-render-log-compare.shs`.
- `/Users/ormastes/simple/bin/simple check` for
  `macos_metal_render_log_compare_spec.spl`,
  `electron_live_smoke_proof_validator_spec.spl`,
  `gui_renderdoc_feature_coverage_status_spec.spl`,
  `renderdoc_electron_html_gate_spec.spl`,
  `tauri_mobile_renderer_parity_evidence_spec.spl`,
  `production_gui_web_renderer_parity_gate_spec.spl`, and
  `gui_widget_renderdoc_goal_status_spec.spl`.

Next concrete integration step: decide whether to materialize the staged
disposable-worktree reconciliation into the feature branch, or continue using
the probe as evidence while resolving any remaining broader `origin/main`
renderer commit equivalence questions.

### Current-Tip Materialization Worktree (2026-07-02)

The staged disposable probe reconciliation was materialized onto the current
feature tip in a clean worktree:

- Worktree: `/tmp/simple-mac-metal-materialize`
- Base commit: `04990d735c6b3e275fd7cd58a67c54a08ddba038`
  (`docs(gui): record renderer hardening reconciliation plan`)
- Patch source: staged diff from `/tmp/simple-mac-metal-reconcile-probe`
- Apply result: `git apply --index --3way` applied all scoped renderer files
  cleanly with no conflicts.
- Materialized files:
  - `doc/03_plan/agent_tasks/gui_web_mobile_renderer_hardening_resume_2026-06-28.md`
  - `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`
  - `scripts/check/check-gui-widget-renderdoc-goal-status.shs`
  - `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`
  - `scripts/check/check-renderdoc-electron-html-gate.shs`
  - `scripts/lib/render-log-common.shs`
  - `test/03_system/check/electron_live_smoke_proof_validator_spec.spl`
  - `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl`
  - `test/03_system/check/macos_metal_render_log_compare_spec.spl`
  - `test/03_system/check/production_gui_web_renderer_parity_gate_spec.spl`
  - `test/03_system/check/renderdoc_electron_html_gate_spec.spl`
  - `test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl`

Materialized current-tip checks passed:

- `sh -n` for all touched shell wrappers listed above.
- `git diff --check --cached` in `/tmp/simple-mac-metal-materialize`.
- Conflict-marker scan across the resolved renderer scripts/specs.
- `/Users/ormastes/simple/bin/simple check` for:
  `macos_metal_render_log_compare_spec.spl`,
  `electron_live_smoke_proof_validator_spec.spl`,
  `gui_renderdoc_feature_coverage_status_spec.spl`,
  `renderdoc_electron_html_gate_spec.spl`,
  `tauri_mobile_renderer_parity_evidence_spec.spl`,
  `production_gui_web_renderer_parity_gate_spec.spl`, and
  `gui_widget_renderdoc_goal_status_spec.spl`.

Materialized commit:

- `9c0806d432dbfbd8f2d74c15df7ae30f2e19fed1`
  (`test(gui): materialize renderer metal reconciliation`)
- Remote ref verified:
  `refs/heads/codex/tauri-mobile-renderer-parity-2026-06-26`.

### Current Evidence Audit (2026-07-02)

Current scoped audit result: **not complete**. The branch sync/reconciliation
commit exists on GitHub, but the Mac GUI/Metal checklist still lacks current
passing evidence artifacts.

Findings:

- `scripts/check/check-macos-metal-render-log-compare.shs` could not run until
  the missing canonical helper `scripts/lib/render-log-common.shs` was restored
  from the `origin/main` helper surface.
- Fresh command:
  `BUILD_DIR=build/mac-gui-metal-current-audit/macos-metal-render-log-compare
  REPORT_PATH=build/mac-gui-metal-current-audit/macos-metal-render-log-compare/report.md
  sh scripts/check/check-macos-metal-render-log-compare.shs`
  emitted:
  - `macos_metal_render_log_compare_status=unavailable`
  - `macos_metal_render_log_compare_required_api=metal`
  - `macos_metal_render_log_compare_generated_readback_gate_status=fail`
  - `macos_metal_render_log_compare_framebuffer_readback_gate_status=fail`
  - `macos_metal_render_log_compare_browser_backing_gate_status=fail`
  - `macos_metal_render_log_compare_pairwise_gate_status=fail`
  - `macos_metal_render_log_compare_argb_source_gate_status=fail`
  - `macos_metal_render_log_compare_blocked_gate_count=8`
  - missing source envs:
    `build/metal_generated_2d_readback/evidence.env`,
    `build/metal_engine2d_framebuffer_readback_evidence/evidence.env`, and
    `build/macos-metal-browser-backing/evidence.env`.
- Fresh command:
  `BUILD_ROOT=build/mac-gui-metal-current-audit/production-gui-web-parity
  REPORT_PATH=build/mac-gui-metal-current-audit/production-gui-web-parity/report.md
  PRODUCTION_GUI_WEB_RENDERER_PARITY_SUBCHECK_TIMEOUT_SECS=120
  sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs`
  emitted:
  - `production_gui_web_renderer_parity_status=fail`
  - `production_gui_web_renderer_parity_reason=electron-layout-manifest-failed`
  - `production_gui_web_renderer_parity_matrix_status=pass`
  - `production_gui_web_renderer_parity_layout_manifest_status=timeout`
  - no current `surface_manifest`, `backend_status`,
    `backend_same_frame_readback`, or `metal_readback_status` rows were emitted.

Next concrete evidence step: produce the three Metal source envs above from
live current macOS artifacts, then rerun the two wrappers once. Do not claim
Mac GUI/Web Metal completion until production parity reaches
`production_gui_web_renderer_parity_status=pass` with exact backend/readback
rows, and the macOS render-log compare reaches
`macos_metal_render_log_compare_status=pass` with `blocked_gate_count=0`.

### Native Metal Source Env Refresh (2026-07-02)

Current scoped result: two of the three source envs now have current macOS
evidence; the remaining blocker is the browser-backed Metal/ARGB env.

Commands and rows:

- `SIMPLE_BIN=/Users/ormastes/simple/bin/simple
  REPORT_PATH=build/mac-gui-metal-current-audit/metal-generated-readback/report.md
  sh scripts/check/check-metal-generated-2d-readback.shs`
  emitted:
  - `metal_generated_2d_readback_status=pass`
  - `metal_generated_2d_readback_reason=gpu-readback-verified`
  - `metal_generated_2d_readback_module_verified=true`
  - `metal_generated_2d_readback_submit_attempted=true`
  - `metal_generated_2d_readback_readback_available=true`
  - `metal_generated_2d_readback_actual_checksum=2935174976`
  - `metal_generated_2d_readback_expected_checksum=2935174976`
- `SIMPLE_BIN=/Users/ormastes/simple/bin/simple
  REPORT_PATH=build/mac-gui-metal-current-audit/metal-framebuffer-readback/report.md
  sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs`
  emitted:
  - `metal_engine2d_framebuffer_readback_status=pass`
  - `metal_engine2d_framebuffer_readback_reason=raw-metal-framebuffer-download-proven`
  - `metal_engine2d_framebuffer_readback_spec_status=pass`
  - `metal_engine2d_framebuffer_gpu_readback_available=true`
  - `metal_engine2d_framebuffer_blur_or_tolerance_used=false`
- Rerunning
  `BUILD_DIR=build/mac-gui-metal-current-audit/macos-metal-render-log-compare-after-native
  REPORT_PATH=build/mac-gui-metal-current-audit/macos-metal-render-log-compare-after-native/report.md
  sh scripts/check/check-macos-metal-render-log-compare.shs`
  emitted:
  - `macos_metal_render_log_compare_status=unavailable`
  - `macos_metal_render_log_compare_generated_readback_gate_status=pass`
  - `macos_metal_render_log_compare_generated_checksum_reason=pass`
  - `macos_metal_render_log_compare_framebuffer_readback_gate_status=pass`
  - `macos_metal_render_log_compare_browser_backing_gate_status=fail`
  - `macos_metal_render_log_compare_pairwise_gate_status=fail`
  - `macos_metal_render_log_compare_argb_source_gate_status=fail`
  - `macos_metal_render_log_compare_blocked_gate_count=4`
  - `macos_metal_render_log_compare_blocked_gates=macos-metal-browser-env,browser-metal-backing,pairwise-argb-diff,argb-source-evidence`

Implementation note: the generated readback pass path now emits the singular
`metal_generated_2d_readback_actual_checksum` and
`metal_generated_2d_readback_expected_checksum` aliases consumed by
`check-macos-metal-render-log-compare.shs`; the per-op checksum rows remain the
stronger readback proof.

Next concrete evidence step: implement or run a current
`build/macos-metal-browser-backing/evidence.env` producer that captures
Electron and Chrome browser GPU metadata showing Metal backing, writes
per-browser source proof files, writes Simple/Chrome/Electron ARGB artifacts for
the same scene, and emits exact pairwise ARGB diff rows. The render-log compare
must not be marked complete until that env is present and the rerun reaches
`blocked_gate_count=0`.

### Browser Metal Backing Producer Refresh (2026-07-02)

Current scoped result: `scripts/check/check-macos-metal-browser-backing-evidence.shs`
now materializes passing browser backing evidence consumed by the macOS Metal
render-log gate. The wrapper captures live Chrome and Electron ARGB artifacts,
writes per-browser scoped GPU source env files plus raw JSON sidecars, and
requires all Simple/Chrome/Electron pairwise ARGB diffs to be exact.

Observed rows from
`BUILD_DIR=build/macos-metal-browser-backing
REPORT_PATH=build/macos-metal-browser-backing/report.md
sh scripts/check/check-macos-metal-browser-backing-evidence.shs`:

- `macos_metal_browser_backing_status=pass`
- `macos_metal_electron_browser_backing_status=pass`
- `macos_metal_electron_browser_backing_gpu_compositing=enabled`
- `macos_metal_electron_browser_backing_gl_implementation_parts=(gl=egl-angle,angle=metal)`
- `macos_metal_chrome_browser_backing_status=pass`
- `macos_metal_chrome_browser_backing_gpu_compositing=enabled`
- `macos_metal_chrome_browser_backing_skia_backend_type=GraphiteDawnMetal`
- `macos_metal_electron_chrome_pairwise_diff_status=pass`
- `macos_metal_electron_simple_pairwise_diff_status=pass`
- `macos_metal_chrome_simple_pairwise_diff_status=pass`
- Simple, Chrome, and Electron ARGB artifacts are present, nonblank, 96x64, and
  share checksum `26305055459328`.

Rerunning `check-macos-metal-render-log-compare.shs` after that producer emitted:

- `macos_metal_render_log_compare_status=pass`
- `macos_metal_render_log_compare_browser_env_file_status=pass`
- `macos_metal_render_log_compare_browser_env_artifact_status=pass`
- `macos_metal_render_log_compare_browser_backing_gate_status=pass`
- `macos_metal_render_log_compare_pairwise_gate_status=pass`
- `macos_metal_render_log_compare_argb_source_gate_status=pass`
- `macos_metal_render_log_compare_blocked_gate_count=0`
- `macos_metal_render_log_compare_blocked_gates=`

Mac GUI/Web Metal render-log comparison is now proven for the local macOS
browser/readback evidence slice. The broader GUI/Web/Mobile hardening goal still
requires production parity and mobile Tauri iOS/Android evidence before the full
plan is done.

### Production Font Offload Evidence Contract (2026-07-02)

The production aggregate now reaches the Metal render-log comparison, but full
GUI/Web parity is still blocked by font offload readiness:

- `production_gui_web_renderer_parity_font_offload_status=unavailable`
- `production_gui_web_renderer_parity_font_offload_reason=vector-font-gpu-glyph-return-missing;runtime-unavailable`

Follow-up hardening in the isolated worktree made the font evidence contract
Metal-aware without weakening the gate:

- `check-production-gui-font-offload-evidence.shs` now runs the real
  `rasterize_vector_accelerated` and `rasterize_bitmap_accelerated` paths.
- Metal proof is consumed through the existing
  `METAL_VECTOR_FONT_GLYPH_*` and `METAL_BITMAP_FONT_GLYPH_*` payloads, so the
  rasterizer records `vector_font_accelerator_stats()` and
  `bitmap_font_accelerator_stats()` before the production evidence is assembled.
- The wrapper emits vector and bitmap accelerator counters for attempts, Metal,
  CUDA, OpenCL, CPU fallback, returned glyphs, and returned glyph pixels.
- `check-production-gui-web-renderer-parity-evidence.shs` forwards those rows
  into the normalized production aggregate namespace.

Focused evidence:

- Default production font evidence remains fail-closed with Metal selected but
  no Metal glyph payload or runtime/readback proof.
- Env-backed Metal glyph/readback evidence passes only after the rasterizers
  accept matching checksum-verified payloads, with
  `production_gui_font_offload_vector_metal_hits=1`,
  `production_gui_font_offload_bitmap_metal_hits=1`,
  `production_gui_font_offload_vector_readback_status=vector-font-glyph-readback-matched`,
  and `production_gui_font_offload_bitmap_readback_status=gpu-glyph-raster-readback-matched`.

Next concrete step: wire a real macOS Metal font producer into those payloads or
explicitly scope font offload out of the production parity acceptance criteria.
Do not mark `production_gui_web_renderer_parity_status=pass` from synthetic
payloads alone.

### macOS Metal Font Payload Producer (2026-07-02)

Follow-up implementation added a native Metal producer for the font payload
contract:

- `check-macos-metal-font-glyph-payload-evidence.shs` runs
  `metal_font_glyph_payload_harness.spl`.
- The harness compiles a small Metal compute kernel, dispatches it, waits for
  command-buffer completion, downloads the buffer, verifies checksum `2064`, and
  emits `METAL_VECTOR_FONT_GLYPH_*` plus `METAL_BITMAP_FONT_GLYPH_*` rows.
- `check-production-gui-font-offload-evidence.shs` runs that producer by
  default and exports only those `METAL_*_FONT_*` rows into the production font
  evidence process.

Observed focused result on macOS:

- `macos_metal_font_glyph_payload_status=pass`
- `macos_metal_font_glyph_payload_submit_attempted=true`
- `macos_metal_font_glyph_payload_readback_available=true`
- `macos_metal_font_glyph_payload_actual_checksum=2064`
- `production_gui_font_offload_status=pass`
- `production_gui_font_offload_metal_payload_status=pass`
- `production_gui_font_offload_vector_metal_hits=1`
- `production_gui_font_offload_bitmap_metal_hits=1`
- vector and bitmap CPU fallback hits are `0`.

Remaining completion requirement: rerun the full production GUI/Web aggregate
without fixture overrides and verify `production_gui_web_renderer_parity_status=pass`
plus the event-routing and mobile Tauri iOS/Android gates. The font blocker is
now resolved at the focused wrapper level on this macOS host.

## Existing Canonical Artifacts

- Feature requirements:
  `doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md`
- NFRs:
  `doc/02_requirements/nfr/production_gui_web_renderer_parity_hardening.md`
- Agent task history:
  `doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md`
- Architecture:
  `doc/04_architecture/ui/production_gui_web_renderer_parity_hardening.md`
- Design:
  `doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md`
- Mobile parity spec:
  `test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl`
- Generated mobile parity manual:
  `doc/06_spec/test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.md`

## Resume Plan

1. Reconcile workspace ownership.
   - Separate current dirty branch work from unrelated generated/vendor/target
     churn.
   - Preserve user/other-agent changes.
   - Decide whether this branch should be rebased/merged onto `origin/main` or
     whether the crash-lane `main` commits should be cherry-picked into it.

2. Reconcile crash-lane commits.
   - Inspect the four known `origin/main` GUI evidence commits listed above.
   - Verify whether their scripts/spec expectations are already represented in
     this branch or need to be ported.
   - Avoid duplicate or contradictory evidence fields.

3. Validate the current dirty renderer/capture work.
   - Confirm direct environment/process access uses approved facades.
   - Confirm browser/file ops moved through owner modules after
     `browser_file_ops.spl` deletion.
   - Confirm updated RenderDoc, HTML/CSS manifest, widget fixture, and Chrome
     bitmap capture changes are real checks, not placeholder passes.

4. Close evidence gaps without false claims.
   - Chrome/Electron desktop evidence must report live capture provenance,
     viewport, format, mismatch count, artifacts, and tolerance policy.
   - iOS evidence must prove Tauri2/WKWebView layout plus Metal render-log
     markers.
   - Android evidence must prove Tauri2/WebView layout plus Vulkan render-log
     markers.
   - Divergent measured results are acceptable diagnostics only when reported as
     divergent, not as parity pass.

5. Run bounded verification.
   - Run each acceptance gate at most once per verify cycle.
   - Stop after three verify/fix cycles and report remaining failures instead
     of repeating green checks.

## Detailed Completion Criteria

Completion requires all of the following evidence in the current workspace:

- Requirements and NFR coverage:
  - REQ-001 through REQ-025 from the production GUI/Web renderer parity
    hardening requirement set are still traceable to implementation and tests.
  - NFR-001 exact parity claims use `mismatch_count=0`, `match=10000`, and
    `max_delta=0`.
  - NFR-002 forbids blur, tolerance, fake capture, and fixture fallback for
    exact parity claims.
  - NFR-006/NFR-007 diagnostic divergences include provenance and never pass as
    exact parity.

- Desktop capture evidence:
  - Chrome live capture evidence exists and distinguishes pass, divergent,
    fail, skip, and unavailable.
  - Electron live capture evidence exists and records native capture size,
    logical size, scale/downsample behavior, GPU/crash diagnostics, viewport,
    artifact paths, and mismatch data.
  - Retina/native-to-logical capture handling is verified where applicable.

- Mobile capture evidence:
  - `check-tauri-mobile-renderer-parity-evidence.shs` fails closed when the
    desktop source evidence is missing or failed.
  - iOS proof includes screenshot/layout evidence, Tauri2/WKWebView identity,
    and Metal markers from logs.
  - Android proof includes screenshot/layout evidence, Tauri2 Android WebView
    identity, and Vulkan markers from logcat or explicit GPU logs.
  - Missing iOS Metal or Android Vulkan markers produce fail reasons, not pass.

- Event and animation evidence:
  - Mobile interaction proof covers at least open-window or equivalent event
    routing markers and ties them to rendered state.
  - Animation/performance claims include captured frame or timing evidence, or
    are explicitly marked as not completed.

- SPipe and docs:
  - Executable specs live under `test/**`, not `doc/06_spec/**`.
  - Generated/manual spec docs under `doc/06_spec/**` match the executable
    specs.
  - The SPipe skill/docs no longer reference obsolete SStack behavior for this
    flow.

- Verification gates:
  - `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.
  - `sh scripts/audit/direct-env-runtime-guard.shs --working` passes.
  - `sh scripts/audit/direct-env-runtime-guard.shs --staged` passes when files
    are staged for commit.
  - Relevant focused SPipe specs pass once in the current session.
  - `git diff --check` passes.
  - Current branch is integrated with required `origin/main` GUI evidence
    commits or explicitly documents why it is intentionally separate.
  - Final pushed branch/ref is verified with `git ls-remote`.

## Non-Completion Signals

- A script accepts missing capture artifacts as parity.
- A tracked divergence is labeled as exact pass.
- A mobile proof has layout evidence but no Metal/Vulkan backend marker.
- Any executable `.spl` spec appears under `doc/06_spec`.
- Verification relies only on generated docs without running the executable
  spec or wrapper that owns the behavior.
- The branch ignores the later `origin/main` crash-lane evidence commits without
  an explicit reconciliation decision.

## 2026-07-02 Mobile Bootstrap Rerun

Desktop production GUI/Web parity evidence remains green in
`build/goal-production-gui-web-parity-current/evidence.env`, including the
Metal render-log gate. A mobile aggregate rerun with explicit host Simple and
Android SDK tools reached the live mobile wrappers but still failed:

- `tauri_mobile_renderer_parity_status=fail`
- `tauri_mobile_renderer_parity_reason=Tauri iOS render log not observed within 120s`
- `tauri_mobile_renderer_parity_ios_status=fail`
- `tauri_mobile_renderer_parity_android_status=fail`
- Android initially built the debug APK, but the package lacked
  `lib/arm64-v8a/libsimple_mobile_runtime_exec.so` because the local
  `src/compiler_rust/target/aarch64-linux-android/release/simple` runtime was
  not present.

Wrapper hardening in this lane now installs local Tauri npm dependencies for
iOS, puts `tools/tauri-shell/node_modules/.bin` on `PATH`, discovers adb and
emulator from the normal macOS Android SDK locations, and rebuilds stale/missing
Android APKs only when the arm64 Simple runtime artifact is available. The
remaining completion blockers are live iOS render-log observation and producing
or supplying the Android arm64 Simple runtime before rerunning the aggregate.

## 2026-07-02 Runtime/Validator Follow-Up

The missing mobile runtime artifacts were produced locally:

- `src/compiler_rust/target/aarch64-apple-ios-sim/release/simple`
- `tools/tauri-shell/src-tauri/ios_runtime_aarch64_sim.bin`
- `src/compiler_rust/target/aarch64-linux-android/release/simple`

The aggregate now has validator scripts for iOS render/Metal/WKWebView log proof
and Android render/Vulkan log proof. The Android evidence wrapper also clears
logcat after APK install and before launching `com.simple.ui`, preventing
unrelated package-install/system crashes from being treated as renderer crashes.

Live rerun in `build/goal-tauri-mobile-after-validator-fix/evidence.env`:

- `tauri_mobile_renderer_parity_ios_status=pass`
- `tauri_mobile_renderer_parity_ios_render_log_validation_status=pass`
- `tauri_mobile_renderer_parity_ios_metal_log_status=pass`
- `tauri_mobile_renderer_parity_android_status=pass`
- `tauri_mobile_renderer_parity_android_render_log_validation_status=pass`
- `tauri_mobile_renderer_parity_android_vulkan_log_status=pass`
- aggregate remains `fail` with
  `tauri_mobile_renderer_parity_reason=ios-screenshot-artifact-proof-missing`
  because live iOS/Android MDI proof rows are still empty.

Next work should connect the existing live MDI proof flow to the aggregate rows
(`*_mdi_proof_json`, render/event/capture/performance/latency/animation detail)
rather than relaxing the mobile completion gate.

## 2026-07-02 MDI Proof Row Normalization

This lane added strict mobile MDI proof normalization and wired the default
mobile renderer wrappers toward the MDI smoke entry:

- `scripts/check/normalize-tauri-mobile-mdi-proof.js` validates the live proof
  JSON and emits the aggregate `ios_mdi_*` / `android_mdi_*` detail rows only
  when render, event routing, viewport, performance, input-to-paint, and
  animation evidence all pass.
- The Tauri shell `MdiProof` payload now includes viewport, DPR,
  orientation, performance.now timing, input-to-paint timing,
  requestAnimationFrame count, CSS animation probe, event sequence, taskbar
  visibility, and source-window count.
- The iOS probe server self-test and standalone iOS MDI wrapper use the same
  stricter proof contract.
- The iOS and Android renderer evidence wrappers set a build-time proof flag so
  mobile evidence mode runs `examples/06_io/ui/tauri_mobile_mdi_smoke.spl`
  instead of the widget showcase bundle; Android also rebuilds the APK when the
  Tauri shell/build script/smoke source is newer than the packaged APK.

Focused verification passed:

- `node --check scripts/check/normalize-tauri-mobile-mdi-proof.js`
- `sh -n scripts/check/check-tauri-ios-mobile-renderer-evidence.shs`
- `sh -n scripts/check/check-tauri-android-mobile-renderer-evidence.shs`
- `SIMPLE_LIB=src /Users/ormastes/simple/bin/simple check scripts/check/ios_mdi_probe_server.spl --mode=interpreter`
- `cargo check --manifest-path tools/tauri-shell/src-tauri/Cargo.toml`
- `SIMPLE_LIB=src /Users/ormastes/simple/bin/simple test test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl --mode=interpreter --clean`

Live aggregate verification was capped after three runs to avoid a runaway
loop. The latest evidence directory is
`build/goal-tauri-mobile-after-proof-flag/`. The proof flag succeeded in
switching iOS to the MDI smoke entry; the iOS dev log shows
`simple-mobile-mdi-smoke.spl` and four `openWindow` messages. The aggregate
still fails before row normalization because MDI smoke mode does not emit the
standard renderer marker:

- `tauri_mobile_renderer_parity_status=fail`
- `tauri_mobile_renderer_parity_reason=Tauri iOS render log not observed within 120s`
- `tauri_mobile_renderer_parity_ios_status=fail`
- `tauri_mobile_renderer_parity_android_status=fail`

Next work should make mobile MDI shell initialization emit the same
`[tauri-shell] render, html_len=` marker that the renderer validators require,
then rerun the aggregate once and inspect the normalized MDI rows.

## 2026-07-02 MDI Render Marker and Android Proof Closure

Follow-up hardening made the bundled MDI smoke path emit the same standard
renderer marker as normal render envelopes:

- `openWindow` and `renderWindow` handling now updates cumulative MDI HTML
  length and logs `[tauri-shell] render, html_len=...`.
- The mobile MDI shell now renders a real `#dock` with `.tab-bar-item`,
  `.tab-bar-icon`, and `.tab-bar-label` nodes so the live proof can validate
  taskbar item/icon counts and visibility.
- The delayed proof eval is requested outside the Rust `mobile` cfg so simulator
  dev builds are not skipped when the cfg differs from Android.
- MDI proof JSON is cleared per wrapper run, and the normalizer prefers the
  newest log proof over any stale proof JSON file.
- The iOS renderer wrapper cleans the `simple-tauri-shell` crate before
  proof-mode `cargo tauri ios dev` so proof-flag/source changes are not hidden
  by stale native artifacts.

Focused verification passed again:

- `node --check scripts/check/normalize-tauri-mobile-mdi-proof.js`
- `sh -n scripts/check/check-tauri-ios-mobile-renderer-evidence.shs`
- `sh -n scripts/check/check-tauri-android-mobile-renderer-evidence.shs`
- `cargo check --manifest-path tools/tauri-shell/src-tauri/Cargo.toml`
- `SIMPLE_LIB=src /Users/ormastes/simple/bin/simple test test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl --mode=interpreter --clean`

Latest live aggregate evidence is in
`build/goal-tauri-mobile-after-proof-rebuild/`:

- `tauri_mobile_renderer_parity_android_status=pass`
- `tauri_mobile_renderer_parity_android_render_log_validation_status=pass`
- `tauri_mobile_renderer_parity_android_mdi_proof_status=pass`
- `tauri_mobile_renderer_parity_android_mdi_event_status=pass`
- `tauri_mobile_renderer_parity_android_mdi_capture_status=pass`
- aggregate remains `fail` with
  `tauri_mobile_renderer_parity_reason=Tauri iOS MDI proof log not observed within 120s`

The iOS log now proves the MDI smoke entry and render markers:
`simple-mobile-mdi-smoke.spl`, four `openWindow` messages, and
`[tauri-shell] render, html_len=...`. It still lacks `[tauri-shell] mdi proof:`.
Next work should focus only on the iOS proof callback path: either make the
Tauri command invoke reachable from iOS WKWebView proof JS or route iOS MDI
proof through the existing URL/probe proof path without weakening the aggregate
MDI detail rows.

## 2026-07-02 iOS WKWebView Proof Transport Fallback

Follow-up work made the proof script retry from inside the WebView and added a
proof-mode localhost fallback transport:

- `maybe_write_tauri_mdi_proof` now installs
  `window.__SIMPLE_TAURI_RUN_MDI_PROOF__` and schedules one in-page delayed
  retry so DOM/taskbar/bridge state is recomputed inside WKWebView.
- The Tauri shell starts a localhost-only `/mdi-proof` receiver in proof mode.
  The WebView sends the same live `MdiProof` JSON over both POST/fetch and a
  GET image beacon fallback, so the data remains live DOM/event/viewport proof
  rather than a Rust-side synthetic payload.
- Focused checks passed:
  `cargo check --manifest-path tools/tauri-shell/src-tauri/Cargo.toml`,
  `cargo test --manifest-path tools/tauri-shell/src-tauri/Cargo.toml tauri_mdi_bootstrap_has_drag_and_desktop_root`,
  `SIMPLE_LIB=src /Users/ormastes/simple/bin/simple test test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl --mode=interpreter --clean`,
  and `git diff --check`.

Live aggregate reruns were capped after two attempts this turn:

- `build/goal-tauri-mobile-webview-delayed-proof/` still failed with
  `tauri_mobile_renderer_parity_reason=Tauri iOS MDI proof log not observed within 120s`.
- `build/goal-tauri-mobile-loopback-proof/` also failed with the same reason,
  but the iOS log now shows the fallback listener starting:
  `[tauri-shell] mdi proof loopback listening on http://127.0.0.1:60136/mdi-proof`.
- Android remains green in the same aggregate:
  `tauri_mobile_renderer_parity_android_status=pass`,
  `tauri_mobile_renderer_parity_android_mdi_proof_status=pass`, and
  `tauri_mobile_renderer_parity_android_mdi_event_status=pass`.

The remaining iOS question is now narrower: WKWebView still does not deliver
the proof payload to Rust. The next live run should test the image-beacon GET
fallback; if it still does not hit the loopback receiver, inspect WKWebView
cleartext/local-network policy or switch the iOS proof lane to the existing
served URL/probe path while preserving the strict normalized MDI rows.
