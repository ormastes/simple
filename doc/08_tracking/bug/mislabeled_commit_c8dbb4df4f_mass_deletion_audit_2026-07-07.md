# Deletion audit: mislabeled commit `c8dbb4df4f` (394 files / 56,398 lines) — still-absent inventory

- **Status:** RECOVERY ROUND 2 COMPLETE — 170 of 244 in-scope files restored;
  remaining 74 confirmed obsolete-by-design (no action needed). `tools/tauri-shell`
  was restored separately (see Related).
- **Priority:** P1
- **Date:** 2026-07-07
- **Area:** repo-wide (compiler variant overlays, dev tooling, one src edit)
- **Related:** `doc/08_tracking/bug/tauri_shell_source_untracked_unreproducible_2026-07-07.md` (RECOVERED),
  `doc/09_report/tauri_shell_source_recovery_investigation_2026-07-07.md`

## Recovery round 2 (2026-07-07) — commits

All restored `git checkout c8756fe7cc -- <path>` verbatim, then committed with `jj commit` scoped per group:

| Group | Files | Commit |
|---|---:|---|
| `variants/**` | 8 | `2e13bd4022d6` — fix(recovery): restore variants/** module-variant overlays deleted by mislabeled c8dbb4df4f |
| `tools/claude-plugin/**` + `tools/mcp-registry/**` + `tools/lsp-mcp-registry/{README.md,package.json,server.json}` | 121 | `2cdc4b5237c8` — fix(recovery): restore tools/claude-plugin + tools/mcp-registry + tools/lsp-mcp-registry metadata (canonical per code-style rules) |
| GUI/render tooling batch (`gui_perf_bench`, `tauri-live-bitmap`, `electron-wasm-gui-exec`, `docker` Dockerfiles, `web-render-backend` chromium-webgpu subdirs, `pixel_compare` remainder, `electron-live-bitmap` remainder, `electron-shell` famous-site scripts) | 40 | `596e8e56c281` — fix(recovery): restore GUI/render tooling dirs deleted by mislabeled c8dbb4df4f |
| `tools/pixel_compare/render_and_save_simple.spl` (gap in this audit's own recovery command reference — table said 5, commands only listed 4) | 1 | `f8217c17` — fix(recovery): restore tools/pixel_compare/render_and_save_simple.spl missed by round-2 batch |

**Total restored: 170 files.** All groups verified: 8/8, 121/121, 40/40 + 1
file counts matched the audit table exactly (the `pixel_compare` group's
command-reference gap is called out and closed above); every restored
`.json` parsed cleanly; every base-file/guide/bug reference named in the
"Still-absent groups" table below now resolves against a real file
(spot-checked:
`.claude/rules/code-style.md` claude-plugin/mcp-registry lines,
`src/lib/nogc_sync_mut/target_ext.spl:7`,
`src/lib/gc_async_mut/gpu/engine2d/renderer_select.spl:11`,
`doc/08_tracking/bug/var_overlay_os_paths_runtime_host_not_buildtime_2026-06-29.md`,
`doc/07_guide/platform/gui_perf_benchmark_comparison.md`,
`doc/07_guide/ui/pixel_comparison_guide.md`,
`doc/07_guide/ui/web_render_backend.md`,
`doc/07_guide/tooling/renderdoc_capture_infra.md:1478`).

Proof run per group:
- `variants/**`: `test/01_unit/lib/gc_async_mut/gpu/engine2d/renderer_select_spec.spl` → 4/4 PASS.
  `test/01_unit/lib/nogc_sync_mut/target_ext_spec.spl` → 1/2 PASS; the one
  failure (`lib_ext` expects `.so`, host returns `.dylib`) is a pre-existing
  Linux-vs-macOS host-detection assumption in the spec itself, unrelated to
  the restored overlay files (which only apply for explicit non-default
  `platform:` targets) — not introduced by this recovery, not fixed here.
- `tools/claude-plugin` + registries: every restored `.json` (`plugin.json`,
  `marketplace.json`, `.lsp.json`, `.mcp.json`, `package.json`, `server.json`)
  parses via `python3 -c "json.load(...)"` with zero failures.
- GUI/render tooling: guide-reference grep spot-check per subdir (all resolve,
  listed above).

Manifests extended (per `.claude/rules/structure.md` FILE.md convention):
root `FILE.md` gained a `variants` root entry + `variants/FILE.md` child-manifest
row + 7 new `tools/` subdirectory rows; `tools/FILE.md` gained the same 7 rows;
new `variants/FILE.md` created declaring `__init__.spl`/`platform`/`ui`.
`sh scripts/check-workspace-root-guard.shs` → `OK`; `--strict` audit shows zero
*new* violations from any restored/added path (only pre-existing repo-wide
strict-mode debt remains, e.g. `doc/06_spec/FILE.md` gaps, `.spipe/host-cpu-runtime-variants`
— out of scope for this recovery).
`sh scripts/check/check-ui-backend-isolation.shs` → `ui_backend_isolation_new=0`
(536 current vs 537 baselined; no new violations introduced by the restore).

**Confirmed-obsolete (no action, unchanged from initial audit):**
`tools/tls_test_server/target/**` (68, cargo build cache),
`var/lib/**` (3, runtime state/WAL snapshots),
`unit/app/ui/async_tui/summary.txt` (1, unreferenced auto-generated artifact),
`Fri` (1, stray/anomalous path, no corresponding source). Total: 73.

170 restored + 73 confirmed-obsolete = 243, one short of 244 — the
remaining 1 is `tools/lsp-mcp-registry/native/simple_lsp_mcp_server`, the
stale compiled binary deliberately **deferred** (not restored, not
obsolete): regenerating it via a fresh build is higher-value than restoring
a stale artifact, per the original audit's own recommendation. This fully
accounts for the original 244 (the 7 net-trim `M` files were never in the
244 count — they still exist and were only trimmed, not deleted).

No restored file conflicted with any current-work file at the same path —
all target paths were confirmed absent from the working tree immediately
before each `git checkout c8756fe7cc --` invocation.

## Summary

Commit `c8dbb4df4f39ffc354763117e72cb4bdf141ede0` ("fix(stage4-it18): re-apply
clobbered edits — is_generic_* emptiness check + HirFunction full-field
construction", 2026-07-03 11:06:42Z) deletes **394 files / 56,398 lines**
under a commit message describing a small, targeted HIR fix. It lands 36
seconds after `c8756fe7cc` (its direct parent, "feat(office): SUMIFS/COUNTIFS/
... (opus lane)"), the classic signature of an unscoped `jj commit` picking up
a working copy silently clobbered by a concurrent session (see
`.claude/rules/vcs.md` and the user's `reference_jj_push_concurrent_agents`
memory note).

`git show --name-status c8dbb4df4f` breaks down as:
- **387** pure deletions (`D`)
- **7** modifications (`M`) that are themselves net-deletions inside
  surviving files (2 compiler files with small trims, 5 `test/03_system/
  engine/physics_*` and `game3d/rollball_production_spec.spl` — not audited
  further here, they still exist and were only trimmed, not deleted)
- Net: 394 files changed, +41 / -56398 lines

Of the 387 deleted files, **376 are still absent from current `HEAD`**; 11
were independently re-added by later commits (see `## Restored later`
below). `tools/tauri-shell` accounts for 132 of the 376 still-absent paths
and is **excluded from this audit** — it is being restored separately as
`doc/08_tracking/bug/tauri_shell_source_untracked_unreproducible_2026-07-07.md`
(status: RECOVERED). That leaves **244 still-absent files** in scope here.

**Recovery command pattern** (same for every path below — `c8756fe7cc` is the
direct parent of the deletion commit, so it holds the last-known-good content
for literally everything deleted):

```bash
git checkout c8756fe7cc -- <path>
```

## Restored later (11 files — no action needed)

Already re-added independently by later commits; confirmed present in `HEAD`
today:

```
test/03_system/check/wm_gui_window_drawing_spec.spl
tools/chrome-live-bitmap/capture_html_argb.js
tools/electron-live-bitmap/capture_html_argb.js
tools/electron-live-bitmap/exact_fixture.js
tools/electron-shell/main.js
tools/electron-shell/package.json
tools/electron-shell/preload.js
tools/node-render-bitmap/exact_fixture.js
tools/node-render-bitmap/simple_web_engine2d_fixture.js
tools/pixel_compare/render_simple_html.spl
tools/web-render-backend/wm_event_check.js
```

## Still-absent groups (244 files, `tools/tauri-shell` excluded)

| Group | Count | Assessment |
|---|---:|---|
| `tools/claude-plugin/**` (codex-research, dev, gemini-ui-design plugins, marketplace + cmm-lsp/obsidian-search plugin manifests) | 115 | **Unnoticed loss — needs recovery.** `.claude/rules/code-style.md` still says "Claude plugins: `tools/claude-plugin/`" but the directory does not exist on disk at all (`git ls-tree HEAD tools/` has no entry). Any AI-CLI-plugin work referencing this path is currently broken. |
| `tools/tls_test_server/target/**` (build cache only — no source files in the deleted set) | 68 | **Obsolete-by-design, no recovery needed.** Every deleted path here is under `target/` (cargo build cache: fingerprints, `.rustc_info.json`, `doc/`, `debug/incremental/*`); there was never any non-`target/` source tracked for this tool. The deletion correctly removed accidentally-committed build artifacts. |
| `tools/electron-shell/*` remaining (12: `analyze_ppm_delta.js`, `calibrate_famous_site_corpus_ink.js`, `generate_famous_site_glyph_atlas.js`, `package-lock.json`, `summarize_famous_site_corpus_*.js` (4), `summarize_famous_site_text_*.js` (3), `sweep_famous_site_text_postprocess.js`, `verify_famous_site_*.js` (2)) | 12 | **Unnoticed loss — needs recovery.** Referenced from `doc/07_guide/ui/browser_engine_implementation.md`, `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md`, and 3 other current plan docs (famous-site-corpus text-rendering fidelity work). `main.js`/`preload.js`/`package.json` came back via a later commit but these analysis/calibration scripts didn't. |
| `tools/web-render-backend/{chromium-webgpu-compute,chromium-webgpu-draw}/{main.js,package.json}`, `chromium_event_check.js`, `chromium_render.js` | 6 | **Unnoticed loss — needs recovery.** Referenced from `doc/07_guide/ui/web_render_backend.md` and `doc/07_guide/lib/gpu_3d/webgpu_guide.md`. |
| `tools/pixel_compare/{argb_json_to_ppm,capture_webkit_argb,diff_argb,diff_ppm}.js`, `render_and_save_simple.spl` | 5 | **Unnoticed loss — needs recovery.** Referenced from `doc/07_guide/ui/pixel_comparison_guide.md` and `scripts/setup/setup-gui-web-2d-vulkan-env.shs`. `render_simple_html.spl` in the same dir came back via a later commit; these 5 didn't. |
| `tools/gui_perf_bench/**` (`bench_gtk.c`, `bench_js.html`, `bench_js_node.js`, `bench_python.shs`, `run_all_benchmarks.shs`) | 5 | **Unnoticed loss — needs recovery.** Entire directory gone; still actively referenced with runnable command examples in `doc/07_guide/platform/gui_perf_benchmark_comparison.md` (lines 76-139), which currently documents commands that cannot run. |
| `tools/electron-live-bitmap/{electron_computed_style,interact_html_controls,renderdoc_display_html}.js`, `package.json`, `simple_web_layout_capture_manifest.txt` | 5 | **Unnoticed loss — needs recovery.** Referenced from `doc/07_guide/tooling/renderdoc_capture_infra.md`, `doc/03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md`, and 2026-07-02/07-03 GUI RenderDoc coverage status reports. |
| `tools/tauri-live-bitmap/**` (`capture_geometry.swift`, `capture_snapshot.swift`, `raw_rgba_to_argb.js`, `webkitgtk_expected_overlays.js`) | 4 | **Unnoticed loss — needs recovery.** Entire directory gone; `doc/07_guide/tooling/renderdoc_capture_infra.md:1478` explicitly names `tools/tauri-live-bitmap/capture_snapshot.swift` as the WKWebView snapshot backend. Same failure class as the `tauri-shell` bug — worth checking whether it was also caught by this same deletion (it was: same commit, same parent). |
| `tools/lsp-mcp-registry/{README.md,server.json,package.json,native/simple_lsp_mcp_server}` | 4 | **Unnoticed loss — needs recovery.** Referenced in `doc/09_report/2026/04/simple_mcp_lsp_mcp_breakage_2026-04-19.md` and `doc/01_research/infra/tooling/spipe_mcp_design_2026-07-01.md`. Note `native/simple_lsp_mcp_server` is a compiled binary — restoring the stale binary is lower value than regenerating it; the `README.md`/`server.json`/`package.json` registry metadata is the part worth restoring as-is. |
| `tools/mcp-registry/{README.md,package.json,server.json}` | 3 | **Unnoticed loss — needs recovery.** `.claude/rules/code-style.md` still says "MCP registry: `tools/mcp-registry/`" but the directory is gone from `HEAD`. |
| `variants/**` (`__init__.spl`, `variants/platform/{linux,mac,windows}/nogc_sync_mut/target_ext.spl`, `variants/ui/renderer/{cpu,metal,vulkan,webgpu}/std/gpu/engine2d/renderer_select.spl`) | 8 | **Unnoticed loss tied to an active bug — needs recovery, highest priority in this audit.** The entire `variants/` overlay directory is gone (`git ls-tree HEAD variants` returns nothing), yet the *base* files that document and depend on it are still present and still reference it: `src/lib/gc_async_mut/gpu/engine2d/renderer_select.spl:11` says "variants/ui/renderer/<value>/std/gpu/engine2d/renderer_select.spl instead", `src/lib/nogc_sync_mut/target_ext.spl:7` says "variants/platform/<value>/nogc_sync_mut/target_ext.spl", and the currently-open bug `doc/08_tracking/bug/var_overlay_os_paths_runtime_host_not_buildtime_2026-06-29.md` names these exact paths. The module-variant-override mechanism is currently running on fallback defaults only because the actual overlay files don't exist. |
| `var/lib/{simple_portal/run-1.json, web_stack_sample/sample.sdn, web_stack_sample/sample.sdn.wal}` | 3 | **Obsolete-by-design, no recovery needed.** These are runtime state/database artifacts (a sample DB + WAL + a single run's JSON output), not source. `var/lib/simple_portal` and `var_resolution_rules` are documented as a *feature design* in `doc/02_requirements/feature/var_resolution_rules.md` / `doc/06_spec/.../web_stack_sample_spec.md`, but the docs describe the mechanism, not this specific committed data snapshot — regenerable by re-running whatever produced it. Likely should never have been tracked (matches the `tls_test_server/target` pattern of accidentally-committed runtime output). |
| `tools/electron-wasm-gui-exec/{main.js,package.json}` | 2 | **Unnoticed loss — needs recovery.** Referenced from `scripts/check/check-gui-wasm-browser-execution-evidence.shs`. |
| `tools/docker/{Dockerfile.cross-language-perf,Dockerfile.test-isolation}` | 2 | **Unnoticed loss — needs recovery.** Referenced from `doc/07_guide/infra/testing/container_testing.md`, `doc/07_guide/compiler/check_perf.md`, and 2 cross-language-perf reports. |
| `unit/app/ui/async_tui/summary.txt` | 1 | **Obsolete-by-design, no recovery needed.** No references found anywhere in `doc/` or `test/`; reads as an auto-generated coverage/summary artifact, not hand-authored source. |
| `Fri` (single top-level entry, no extension) | 1 | **Noise — not a real deletion of value.** Appears to be a stray/anomalous path (possibly from a filename containing a literal space or a shell-quoting artifact in the original commit). Not investigated further; recommend a follow-up `git show c8dbb4df4f -- Fri` if this matters, but it does not appear to correspond to any documented tool or source file. |

## Recommended follow-ups (priority order)

1. **`variants/**` (8 files)** — restore first; it's the only group tied to
   a currently-open, still-relevant bug (`var_overlay_os_paths_runtime_host_
   not_buildtime_2026-06-29.md`) and affects compiler behavior, not just
   dev tooling docs.
2. **`tools/claude-plugin/**` (115 files) + `tools/mcp-registry/**` (3
   files) + `tools/lsp-mcp-registry/**` metadata (3 of 4 files, skip the
   stale binary)** — restore together; both are named as canonical
   locations in `.claude/rules/code-style.md` today.
3. **GUI/render tooling group** (`tools/gui_perf_bench`,
   `tools/tauri-live-bitmap`, `tools/electron-live-bitmap` remainder,
   `tools/web-render-backend` chromium-webgpu subdirs, `tools/pixel_compare`
   remainder, `tools/electron-shell` famous-site scripts,
   `tools/electron-wasm-gui-exec`, `tools/docker` Dockerfiles) — all
   individually referenced by current guides/plans/check-scripts; restore
   as a batch with `git checkout c8756fe7cc -- <path>` per path, then spot
   check each guide's documented command still runs.
4. **No action**: `tools/tls_test_server/target/**`, `var/lib/**`,
   `unit/app/ui/async_tui/summary.txt`, `Fri`.

## Recovery command reference

```bash
# Highest priority
git checkout c8756fe7cc -- variants

# Plugin/registry docs currently point at these
git checkout c8756fe7cc -- tools/claude-plugin tools/mcp-registry
git checkout c8756fe7cc -- tools/lsp-mcp-registry/README.md tools/lsp-mcp-registry/server.json tools/lsp-mcp-registry/package.json

# GUI/render tooling batch
git checkout c8756fe7cc -- \
  tools/gui_perf_bench \
  tools/tauri-live-bitmap \
  tools/electron-wasm-gui-exec \
  tools/docker/Dockerfile.cross-language-perf tools/docker/Dockerfile.test-isolation
git checkout c8756fe7cc -- tools/web-render-backend/chromium-webgpu-compute tools/web-render-backend/chromium-webgpu-draw tools/web-render-backend/chromium_event_check.js tools/web-render-backend/chromium_render.js
git checkout c8756fe7cc -- tools/pixel_compare/argb_json_to_ppm.js tools/pixel_compare/capture_webkit_argb.js tools/pixel_compare/diff_argb.js tools/pixel_compare/diff_ppm.js
git checkout c8756fe7cc -- tools/electron-live-bitmap/electron_computed_style.js tools/electron-live-bitmap/interact_html_controls.js tools/electron-live-bitmap/renderdoc_display_html.js tools/electron-live-bitmap/package.json tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt
git checkout c8756fe7cc -- tools/electron-shell/analyze_ppm_delta.js tools/electron-shell/calibrate_famous_site_corpus_ink.js tools/electron-shell/generate_famous_site_glyph_atlas.js tools/electron-shell/package-lock.json tools/electron-shell/summarize_famous_site_corpus_coverage.js tools/electron-shell/summarize_famous_site_corpus_reports.js tools/electron-shell/summarize_famous_site_text_color_histogram.js tools/electron-shell/summarize_famous_site_text_compositing.js tools/electron-shell/summarize_famous_site_text_mask_overlap.js tools/electron-shell/sweep_famous_site_text_postprocess.js tools/electron-shell/verify_famous_site_corpus_completion.js tools/electron-shell/verify_famous_site_production_probe.js
```

Not performed in this pass (audit only, per task scope) — these become
follow-up restore items.
