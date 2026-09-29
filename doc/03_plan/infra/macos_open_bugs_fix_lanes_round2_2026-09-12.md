# macOS Open Bugs — Fix Lanes, Round 2 (2026-09-12)

Base: `origin/main@f38ceb0f804` (PR #584-#642 merged). Supersedes round 1
(`macos_open_bugs_fix_lanes_2026-09-12.md`) by re-triaging its items against
today's PR bodies (#584 #587 #588 #591 #594 #596 #599 #601 #602 #604) plus a
fresh bug-db/TODO scan. Host: macOS arm64, Apple M4, seed
`build/cargo-r2/release/simple`, Vulkan+Metal, no RenderDoc, Chrome present.

## (a) Round-1 residuals — carried forward, status corrected today

| item | round-1 lane | today's evidence | status now |
|---|---|---|---|
| Stage 2 `serialize_mir_function` SEGV | 1 | PR #587: only remaining Stage-2 blocker per the 09-06 record's own evidence; **not re-reproduced** — a `--stop-after-stage2` run spent 18m35s just on cold seed build before reaching it | OPEN, unverified this pass — re-run needs a dedicated >30min lane |
| `manifest-verify.shs` 19 `/proc` refs | 1 | PR #587: `grep -c '/proc' manifest-verify.shs` = 19, byte-identical to 09-06; blocker A (smoke-driver procfs) is CLOSED (fixed `e1c40702a20`), this one is not | OPEN, confirmed unchanged today |
| Stale bootstrap ownership lock, dead-PID owner not reclaimed | 1 (note) | not mentioned in any of today's 10 PRs | OPEN, still unfiled — file as new bug this round |
| spipe docgen blocked on deployed self-hosted CLI | 5 | no PR today touched docgen; still gated on Stage 4 | OPEN, unchanged, blocked transitively on lane 1 |
| `check-test-tree-divergence-delta.shs` 20+min / hangs at load~20 | 2/5 (note) | not mentioned today | OPEN, still unfiled — file as new bug this round |
| `metal_engine2d_readback_spec`-class oracles | 4 | round-1 marked "done" | CLOSED — no action |
| `backend_metal_font_spec` (`font_destination_origin(-2147483648,0,2).?`) | 4 (new) | not addressed by #584-#642 | OPEN, unverified — needs the timed re-run below |
| `backend_vulkan_image_exact_scratch_spec` upload counters read zero | 4 (new, PR #642) | PR #642 note only, not fixed | OPEN, unverified |
| `vulkan_resident_2d` 4/11, `rect_list` 0/1, `mask_plane` 4/6, `draw_ir_adv_spec` 69/25, `simple_web_renderer_spec` 39/110, `anonymous_block_spec` 4/4 | 4 (new) | claimed identical on pristine main by today's agents, not independently re-run here | OPEN, **unverified in this pass** — no seed binary was available in this worktree checkout (`build/cargo-r2/release/simple` lives outside the worktree and was not rebuilt); re-run each with `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 <seed> run <spec>`, 300s cap, one at a time, before starting lane 4 work |

New from today's PRs (not in round 1):
- PR #599: `c_runtime_compiles_guard_red_on_macos_aarch64` is now **FIXED** (upstream via #455's `st_mtim` guard) — `PASS — 143 file(s) compiled, 0 errors (6 skipped)`. Remove from lane 2.
- PR #599: found and fixed a blocking push gate that died with a shell trace and no verdict — already landed, no residual.
- PR #591: `check-vulkan-2d-c-compare.shs` C leg now reaches `c_status=admitted` on real MoltenVK; only `simple`-leg stays `skipped:no-selfhosted-simple-binary` — this is now purely a lane-1 (self-hosted CLI) dependency, not an independent lane-4 item. Fold into lane 1's oracle.
- PR #588: redeploy still BLOCKED; `--build-candidate` fails closed `policy-not-prepared` correctly (no defect, expected).
- PR #584: `bin/simple test` fast-fails with a spurious timeout on the `wm_metal_glass_multi_receipt_opacity` specs (reproduces `macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot`, lane 3); `bin/simple run` gets further but hits an import-resolution difference — new, unfiled sub-symptom, fold into lane 3.

## (b) Fresh DB/TODO scan (new items only)

| id | title | file:line | status |
|---|---|---|---|
| gui_smf_dynlib_hot_call_runtime_missing_2026-06-01 | macOS arm64 `.dylib` SMF hot-call evidence still missing (Linux-only evidence passes) | src/app/gui_perf/smf_dynlib_probe.spl:0 | bug_db still lists **open** (P3) — round 1 excluded it as CLOSED; **status conflict, needs reconciliation before scheduling** |

No other new macOS/Metal/Vulkan/dylib/CoreText/IOSurface bug_db or TODO.md rows beyond round 1's set and the table above.

## Lanes (≤1 agent-day each, disjoint files)

**Lane 1 — macOS bootstrap chain to a deployed self-hosted CLI (highest value; blocks `simple test`/lint/docgen/vulkan-simple-leg).**
Files: `scripts/bootstrap/**`, `scripts/check/manifest-verify.shs`, `src/compiler_rust` Stage-2 MIR serialization (`serialize_mir_function`), `bootstrap/stage*/simple` tracked artifacts.
Items: Stage-2 `serialize_mir_function` SEGV (re-reproduce first, budget 45min for cold seed build alone), 19 `/proc` refs in `manifest-verify.shs`, stale ownership lock (file bug first), macos_bootstrap_lane_platform_defect_cluster.
Fixable here: partial (SEGV needs a live repro; `/proc` port has a precedent — `darwin-pinned`).
Oracle: `--stop-after-stage2` exits 0; `grep -c '/proc' manifest-verify.shs` → 0 or all guarded.
Verify: `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2` (budget 1+ hour).

**Lane 2 — Crashes (native runtime faults).**
Files: `src/os/compositor/host_compositor_core.spl` (Vulkan empty-batch fault), `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_image_exact_scratch_spec.spl` (upload counters read zero — may be a real crash-adjacent readback bug, not just wrong output).
Items: macos_vulkan_2d_vector_font_empty_batch_native_fault, backend_vulkan_image_exact_scratch_spec counters.
Size: S each. Fixable: yes.
Oracle: empty-batch fixture no longer faults; counters non-zero on a real upload.
Verify: run each spec directly, 300s cap.

**Lane 3 — Wrong output / blocked test runner.**
Files: `src/app/test_runner_new/**` (inline-`unsafe` parse block, ulimit wiring, timeout-vs-run discrepancy from PR #584), `backend_metal_font_spec.spl`.
Items: macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot, test_runner_ulimit_caps_unusable_on_macos, `bin/simple test` spurious timeout / `bin/simple run` import-resolution gap (PR #584), `backend_metal_font_spec` origin bug.
Size: M. Fixable: yes.
Oracle: `simple test <dir>` and `simple run <spec>` agree; font spec passes or has a filed root cause.
Verify: `bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl`; re-run the 5 `wm_metal_glass` specs from PR #584 with both `test` and `run`.

**Lane 4 — Red specs by owner module (engine2d/Vulkan/web-renderer).**
Files: `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_resident_2d*`, `rect_list*`, `mask_plane*`, `draw_ir_adv_spec.spl`, `test/.../simple_web_renderer_spec.spl`, `anonymous_block_spec.spl`.
Items: the 6 red-spec counts cited in the prompt — **unverified this pass**, must be individually re-run (`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0`, 300s each, serially) before any fix work starts, since no seed binary was buildable in this isolated worktree.
Size: L (6 independent specs, verification alone is ~30min serial).
Fixable: yes, once each failure is confirmed real and macOS-specific (vs. cross-platform pre-existing).
Oracle: each spec's pass count matches its total, or a filed bug explains the gap.
Verify: one spec at a time as above; do not batch (repo-wide guidance: batching multiplies lint/run cost superlinearly).

**Lane 5 — Infra/gates.**
Files: `scripts/check/check-test-tree-divergence-delta.shs` (20+min hang under load ~20 — file first), `scripts/check/check-vulkan-2d-c-compare.shs` (now only blocked on lane-1's self-hosted CLI, no independent fix needed), `.github/workflows/rust-bootstrap-multiplatform.yml` (freetype), `scripts/check/build-macos-es-history-collector.shs` (ES evidence, entitlement-blocked).
Items: divergence-delta hang (new, unfiled), freetype CI gap, ES evidence blocker (documented-blocked, no code fix expected).
Size: S-M. Fixable: yes for freetype/hang; partial for ES (needs TCC/root).
Oracle: divergence-delta guard returns a verdict inside 5min under normal load; CI workflow green.
Verify: `sh scripts/check/check-test-tree-divergence-delta.shs <BASE> <NEW>` with a wall-clock cap; `gh workflow run rust-bootstrap-multiplatform.yml`.

**Lane 6 — Docs/status reconciliation.**
Files: `doc/08_tracking/bug/bug_db.sdn` (gui_smf_dynlib_hot_call_runtime_missing status conflict), `doc/08_tracking/bug/wm_metal_glass_multi_receipt_opacity_2026-07-27.md` (still needs live Metal receipt per round 1, now entangled with lane-3's test-runner blocker per PR #584).
Items: gui_smf_dynlib_hot_call_runtime_missing status conflict, wm_metal_glass_multi_receipt_opacity evidence capture (blocked transitively on lane 3).
Size: S. Fixable: yes (docs only).
Oracle: bug_db status matches actual repo state with a citation; Metal receipt captured once lane 3's test-runner blocker clears.
Verify: none needed beyond doc diff review.

## Unclassified
None. Every round-1 carryover, every today's-PR residual, and the one new
bug_db conflict are assigned to a lane above.
