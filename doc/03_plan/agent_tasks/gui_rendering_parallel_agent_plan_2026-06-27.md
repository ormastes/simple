# GUI Rendering Parallel Agent Plan - 2026-06-27

## Goal

Advance the active SPipe lane for GUI hardening, web-renderer hardening, 2D
Metal/Vulkan backing, and retained 4K/8K GUI showcase performance evidence.

This plan is explicitly parallel-agent oriented. Spark sidecars may discover
gaps or draft small isolated patches, but Spark output is not accepted as done
until reviewed by the main agent or a normal/high-capability review agent.
If Spark quota is unavailable, use mini fallback sidecars for the same lane and
record that the fallback output is advisory under the same review gate.

Do not read any passing Linux/browser/Vulkan/retained-perf row as final goal
completion. Completion still requires fresh source-aligned aggregate evidence
for the relevant row, real RenderDoc `.rdc` artifacts with `RDOC` magic where
required, platform render-log comparison, and separate full-CSS closure.

## Current Baseline

- Baseline must be resolved from the current jj parent or `main@origin` at the
  time an agent starts. Do not reuse stale hashes from older evidence reports.
- 4K retained widget showcase evidence is current and passing in the retained
  evidence row used by the aggregate gate; see
  `doc/09_report/gui_showcase_4k_8k_perf_refresh_2026-06-27.md`.
  Final completion still requires the aggregate `GUI_SHOWCASE_REQUIRE_CURRENT_SOURCE_REVISION=1`
  check to prove source freshness.
- 8K retained widget showcase evidence is current and passing in the retained
  evidence row used by the aggregate gate; use the same retained perf reports
  above and require current-source aggregate validation before final claims.
- Browser Vulkan backing evidence is current and passing for Electron and
  Chrome on the Linux host; see
  `doc/09_report/gui_web_2d_linux_vulkan_refresh_2026-06-27.md` for the
  current refresh and
  `doc/09_report/gui_web_2d_linux_renderdoc_host_blocker_2026-06-27.md` for
  the current RenderDoc host blocker.
- Direct Electron/Chrome/Simple ARGB comparison evidence is current and passing
  from `setup-gui-web-2d-vulkan-env.shs --run`; the aggregate reports
  `gui_web_2d_vulkan_pixel_comparison_status=pass`,
  `gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff`, and all three
  pairwise diff statuses as `pass`; see
  `doc/09_report/gui_web_2d_vulkan_direct_run_artifacts_2026-06-27.md`.
- Web WM modern shell evidence is no longer a blocker after the PATH fallback
  evidence slice.
- RenderDoc `.rdc` capture remains blocked for this current host session by
  missing `renderdoccmd` in the searched paths. Older reports that found
  RenderDoc tooling are dated diagnostics; current completion must use fresh
  host discovery plus real `.rdc` files with `RDOC` magic.
- The active completion blockers remain native RenderDoc `.rdc` evidence,
  platform render-log comparison on Linux/macOS/Windows, and full CSS
  specification coverage beyond the implemented Simple Web subset. Existing
  Darwin production parity/font/raw-Metal reports are not reopened by this
  Linux host plan; any final completion claim still needs the aggregate gate to
  accept the relevant fresh evidence rows.
- Current full-CSS evidence keys remain incomplete:
  `html_css_full_rendering_goal_status=incomplete`,
  `html_css_full_rendering_goal_full_css_rendered_count=133`, and
  `html_css_full_rendering_goal_full_css_unrendered_count=261`.
  `aspect-ratio` and `object-fit` are completed narrow implemented-CSS slices.

## Current Parallel Start Status

Spark was explicitly requested for this replan. The first Spark sidecar fan-out
was attempted in this session for Lane A and Lane B, but both Spark agents
returned a quota error: GPT-5.3-Codex-Spark usage limit reached until 5:04 AM.
Do not mark Spark work as completed from that failed start.

A later Spark restart attempt was made for the same split lanes:

- `Russell` (`gpt-5.3-codex-spark` explorer): Lane A evidence gap scan.
- `Tesla` (`gpt-5.3-codex-spark` explorer): Lane B platform runbook/key
  matrix.

Both failed at the same Spark quota gate. Treat these as start attempts only,
not completed agent work and not evidence. The lane prompts remain valid for a
future Spark restart after quota recovers.

Fallback normal sidecars were started immediately so the lane still proceeds in
parallel:

- `Erdos` (`gpt-5.4-mini` explorer): plan/doc gap scan for GUI/Web/2D
  RenderDoc, Vulkan/Metal/D3D12, and 4K/8K perf.
- `Bohr` (`gpt-5.4-mini` explorer): wrapper/evidence-key matrix for Vulkan
  RenderDoc, browser backing, widget RenderDoc goal, Linux render-log compare,
  and 4K/8K perf.
- `Ampere` (`gpt-5.4` explorer): normal review of this replanned doc and the
  fallback sidecar findings.
- Current fallback fan-out:
  - `Feynman` (`gpt-5.4-mini` explorer): Lane A evidence gap scan after the
    latest Spark quota failure.
  - `Mill` (`gpt-5.4-mini` explorer): Lane B platform runbook/key matrix after
    the latest Spark quota failure.
  - `Poincare` (`gpt-5.4` explorer): normal/high-capability review of the
    updated plan and dirty-file scope.

When Spark quota returns, restart the same Lane A and Lane B prompts with
`gpt-5.3-codex-spark`. Do not mark the earlier quota-failed Spark agents as
complete, and do not advance any Spark finding to integration until Lane C or
the main agent reviews the specific current files or fresh command output named
by Spark.

Fallback sidecar findings accepted for planning only:

- Add an explicit 4K/8K retained-showcase work order instead of leaving perf
  evidence only as report text.
- Treat older queue/readback and platform-matrix plans as candidate stale-doc
  followups, not as blockers for this replan.
- Spark may collect diagnostics, readiness output, and report pointers. Proof
  rows and completion gates remain advisory until Lane C verifies fresh host
  evidence.
- Normal/high-capability review must accept ARGB equivalence, native render-log
  comparison, RenderDoc `.rdc` proof, no-raw-`rt_*` checks, and final 4K/8K
  performance claims.
- Sidecar citations to older `2026-06-26` reports are advisory only. Current
  completion claims must come from fresh aggregate output or retained evidence
  envs aligned to the current source revision.

## Shared Interface Contract

Agents must use these names consistently:

- Aggregate gate: `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`
- Web WM wrapper: `scripts/check/check-web-wm-modern-shell-evidence.shs`
- Vulkan host setup: `scripts/setup/setup-gui-web-2d-vulkan-env.shs`
- 4K/8K perf wrapper: `scripts/check/check-widget-showcase-4k-200fps.shs`
- Completion evidence: `blocked_completion_gates`
- Web WM pass keys:
  - `web_wm_modern_shell_evidence_status=pass`
  - `web_wm_modern_shell_evidence_bitmap_nonblank_status=pass`
  - `web_wm_modern_shell_evidence_audit_pass=pass`
  - `web_wm_modern_shell_evidence_interaction_pass=pass`
- Browser backing pass key: `gui_web_2d_vulkan_browser_backing_status=pass`
- RenderDoc artifact proof requires `RDOC` magic, not only an env row.

## Lane A - Spark Evidence Gap Scan

Owner: Spark sidecar. Current fallback: mini sidecar when Spark quota is
unavailable.

Write scope: none by default. If a tiny patch is proposed, it must be listed
explicitly and reviewed before integration.

Task:

1. Read the current aggregate evidence and guide docs.
2. Produce a ranked list of host-actionable gaps that can be advanced without
   Linux RenderDoc installation.
3. Identify any key-name mismatches like the Web WM `*_path` issue.
4. Do not rerun broad checks or claim completion.

Deliverable:

- Short report with file paths, evidence keys, and the next smallest patch.

Review gate:

- Main agent verifies every claimed gap against current files or command output.
- Lane C normal/high-capability review must reject any Spark conclusion that
  treats missing RenderDoc, platform host, or full CSS evidence as complete.

Spark restart prompt:

```text
Inspect current GUI/Web/2D RenderDoc/Vulkan/Metal/D3D12 hardening and 4K/8K
perf docs. Do not edit. Return existing plan docs, stale baseline claims,
missing parallel lanes, recommended Spark-suitable tasks, normal-review tasks,
and files needing update. Treat the current `main@origin`/working-copy parent
revision as the baseline; do not rely on stale hashes copied from older reports.
```

## Lane B - Spark Platform Runbook Split

Owner: Spark sidecar. Current fallback: mini sidecar when Spark quota is
unavailable.

Write scope: `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md` and related plan
docs only if the sidecar is asked to patch after review.

Task:

1. Split remaining platform work into Linux Vulkan, macOS Metal, and Windows
   D3D12/DXGI/Pix verification lanes.
2. Make clear which evidence can be prepared on this host and which must be run
   in another platform GUI environment.
3. Include RenderDoc, Metal GPU capture, PIX, and native render-log comparison
   acceptance keys.
4. Preserve the rule that fallback screenshots are not backend proof.

Deliverable:

- Proposed runbook delta or patch outline.

Review gate:

- Normal/high-capability review checks backend-specific claims before merge.
- Main agent checks every proposed command against the existing wrapper names
  and evidence keys before committing doc changes.

Spark restart prompt:

```text
Inspect wrappers and evidence keys for GUI/Web/2D Vulkan RenderDoc, browser
backing, widget RenderDoc goal, Linux Vulkan render-log compare, macOS Metal
render-log compare, Windows D3D12 render-log compare, and 4K/8K showcase perf.
Do not edit. Return command/key matrix and identify Spark-runnable lanes versus
normal-agent review lanes. Treat fallback screenshots as non-proof.
```

Accepted reviewed split:

- Linux Vulkan lane: host readiness, browser Vulkan backing, direct ARGB
  comparison, RenderDoc `.rdc`, and Linux render-log normalization.
- macOS Metal lane: native Metal readback, render-log normalization, and GPU
  Capture evidence when capture is required.
- Windows D3D12 lane: native D3D12/DXGI readback, render-log normalization,
  PIX evidence, and GPU-debugger capture evidence.

Host-preparable here:

- Runbook text, evidence schema, Linux Vulkan readiness checks, browser-backing
  checks, capture plumbing, and Linux aggregate/render-log verification.

Requires another GUI platform:

- macOS Metal proof on a real Darwin host with Metal tooling.
- Windows D3D12/PIX/GPU-debugger proof on a real Windows host with native
  capture tools.

Platform acceptance keys:

- Linux: `gui_web_2d_vulkan_browser_backing_status=pass`,
  `gui_web_2d_vulkan_electron_browser_backing_status=pass`,
  `gui_web_2d_vulkan_chrome_browser_backing_status=pass`,
  `gui_web_2d_vulkan_simple_backend_status=pass`,
  `linux_vulkan_render_log_compare_status=pass`,
  `linux_vulkan_render_log_compare_required_api=vulkan`, and
  `linux_vulkan_render_log_compare_pairwise_status=pass`.
- macOS: `readback_metal_verdict=pass`,
  `macos_metal_render_log_compare_status=pass`,
  `macos_metal_render_log_compare_required_api=metal`,
  `macos_metal_render_log_compare_pairwise_status=pass`, and
  `macos_metal_render_log_compare_gpu_capture_status=pass` when GPU capture is
  required.
- Windows: `directx_native_gate_status=pass`,
  `windows_d3d12_render_log_compare_status=pass`,
  `windows_d3d12_render_log_compare_required_api=d3d12`,
  `windows_d3d12_render_log_compare_pairwise_status=pass`,
  `windows_d3d12_render_log_compare_pix_status=pass`, and
  `windows_d3d12_render_log_compare_gpu_debugger_status=pass`.

Anti-overclaim rules:

- Cached screenshots, bitmap parity, and render-log presence are not backend
  proof by themselves.
- Chrome/Electron installs and launch flags are not proof unless browser
  backing keys pass.
- RenderDoc `.rdc` existence is capture evidence only; pixel equivalence still
  requires the pairwise ARGB diff rows.
- Windows `swapchain_present` or presentation provenance is not device readback.

## Lane C - Normal Review Agent

Owner: normal/high-capability review agent.

Write scope: none unless explicitly requested after findings.

Task:

1. Review Spark Lane A and Lane B outputs when available.
2. Review mini fallback outputs from `Erdos` and `Bohr` for this session until
   Spark quota is available.
3. Check for overclaiming, stale evidence, missing file-status rows, and
   accidental acceptance of unavailable host states.
4. Recommend which sidecar output is safe to integrate.

Deliverable:

- Findings ordered by severity with file/key references.

Review gate:

- Main agent integrates only reviewed changes.

Current review checklist:

- Treat Spark or mini sidecar output as advisory until verified against current
  files or fresh command output.
- Reject completion claims while backend capture, platform render-log
  comparison, full CSS coverage, production parity, or RenderDoc `.rdc` gates
  remain incomplete.
- Reject source changes that add raw `rt_*`, direct backend field pokes,
  fixture-only runtime aliases, or tool-local runtime shortcuts in GUI, web,
  2D, benchmark, or evidence wrappers unless the design explicitly approves a
  compatibility shim and a facade owner is documented.
- Reject stale evidence copied from older reports without current source
  alignment.
- Keep `simple-runtime-unavailable`, missing artifacts, and missing
  `renderdoccmd` as blockers, not pass states.
- Require actual `RDOC` magic for RenderDoc capture claims.
- Require file paths and file-status rows for every claimed artifact.

## Lane D - Main Agent Integration

Owner: main Codex session.

Write scope:

- Focused wrappers under `scripts/check/` or `scripts/setup/`.
- Matching SSpec under `test/03_system/check/`.
- Generated/manual docs under `doc/06_spec/`.
- Operator docs under `doc/07_guide/`.
- Reports under `doc/09_report/` when fresh evidence is produced.

Task:

1. Keep the jj worktree clean before delegation and before sync.
2. Integrate only disjoint, reviewed changes.
3. Run bounded verification once per acceptance criterion.
4. Commit, fetch/rebase, and push after each coherent slice.

This session's immediate integration target:

1. Refresh this plan's baseline and sidecar execution state.
2. Start Spark lanes if quota allows; otherwise start mini fallback sidecars and
   keep Spark lanes queued.
3. Collect sidecar outputs once, review them, and update only the task plan or
   narrow docs needed to prevent the next agents from repeating stale work.
4. Treat renderer source and broad wrapper edits as separate implementation
   work orders. This session's current dirty renderer/wrapper/spec/report files
   belong to WO-11 object-fit, not to the Spark replan lane.

## Parallel Work Orders

| Work order | Primary agent | Spark suitability | Write scope | Acceptance evidence |
| --- | --- | --- | --- | --- |
| WO-1 Evidence gap scan | Spark Lane A, mini fallback now | High: read-only search and key comparison | None unless reviewed | Ranked gap list maps to existing files and aggregate keys |
| WO-2 Wrapper/key matrix | Spark Lane B, mini fallback now | High: read-only matrix extraction | None unless reviewed | Commands and pass/blocker keys match current wrappers |
| WO-3 Sidecar review | Normal/high-capability Lane C | Not Spark: review must catch overclaiming | None by default | Findings accept/reject each sidecar claim |
| WO-4 Plan/doc integration | Main agent | Not delegated | `doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md` and directly referenced guides only | Baseline names current commit, Spark status, review gates, and next host lanes |
| WO-5 Linux Vulkan host execution | Future platform agent on prepared Ubuntu GUI host | Medium: Spark may run readiness probes only under supervision | Evidence dirs and reports only | Browser backing and direct ARGB pairwise diff pass first; strict Linux render-log compare remains blocked until Chrome/Electron/Simple RenderDoc `.rdc` artifacts have `RDOC` magic |
| WO-6 macOS Metal host execution | Future Darwin agent | Medium: Spark may collect logs; normal review required | Evidence dirs and reports only | Native Metal readback, GPU capture if required, and macOS render-log compare pass |
| WO-7 Windows D3D12 host execution | Future Windows agent | Low/medium: Spark can collect command output; normal review required | Evidence dirs and reports only | Native D3D12/DXGI readback, PIX/GPU-debugger proof, and Windows render-log compare pass |
| WO-8 4K/8K perf freshness | Main or supervised perf sidecar | Medium: Spark can check retained rows; normal review required for perf claims | Reports/metrics only | Retained rows include viewport, source revision, timing, RSS, checksum/readback, and fallback state |
| WO-9 Stale planning cleanup | Spark scan followed by normal review | High for discovery, review required for edits | `doc/03_plan/agent_tasks/gui_web_host_gpu_queue_readback_spark_tasks.md`, `doc/03_plan/agent_tasks/gui_web_gpu_host_platform_matrix.md`, and directly referenced stale plan docs | Older queue/readback and platform-matrix docs either point to current aggregate/runbook evidence or are explicitly marked historical/superseded |
| WO-10 CSS aspect-ratio slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, focused unit/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `132/132`, and no full-CSS/native-platform completion is claimed |
| WO-11 CSS object-fit slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, Electron bitmap evidence fixture, focused unit/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `133/133`, and no full-CSS/native-platform completion is claimed |
| WO-12 Spark restart queue | Main agent or future orchestrator | High: same read-only prompts after quota recovers | None | New Spark outputs are explicitly compared against `Feynman`/`Mill` fallback results and accepted only after `Poincare`-style normal review |

WO-12 rule: do not spawn Spark against source-edit scopes until the read-only
gap/matrix lanes complete and a normal reviewer approves the intended write
scope. Spark may draft a patch only after the main agent gives a disjoint file
set and a fail-fast acceptance checklist.

WO-8 status: refreshed on 2026-06-27 in
`doc/09_report/gui_showcase_4k_8k_perf_refresh_2026-06-27.md`. The current
host produced passing retained 4K and 8K rows with source revision
`56a1985b1d38`, current-source aggregate validation, checksum/readback proof,
RSS under budget, and `fallback_state=none`.

WO-9 status: the two explicit stale agent-task docs now carry 2026-06-27
superseded/merged routing headers. Future cleanup may still classify deeper
historical plan docs, but agents should no longer treat those two June 14
matrix/handoff files as the active top-level plan.

WO-9 follow-up, 2026-06-27: the queue/readback Spark packet, the 2026-06-26
GUI RenderDoc feature-coverage snapshot, and the GUI/web/2D Vulkan RenderDoc
bug tracker now explicitly distinguish historical RenderDoc availability from
current host proof. Agents must use fresh `--check` discovery and `.rdc` magic,
not stale `ready` rows, for current completion claims.

WO-10 status, 2026-06-27: `aspect-ratio` moved into implemented Simple Web CSS
with focused unit coverage and full-goal status coverage. Current evidence is
recorded in
`doc/09_report/html_css_full_rendering_goal_status_aspect_ratio_2026-06-27.md`:
implemented CSS is `132/132`, full CSS is `132/394`, full CSS unrendered is
`262`, and unsupported inventory ownership is `269`. This is a completed narrow
CSS renderer slice, not completion evidence for full CSS, RenderDoc, Metal, or
D3D12 lanes.

WO-11 status, 2026-06-27: `object-fit` moved into implemented Simple Web CSS
with focused image-placeholder pixel coverage and full-goal status coverage.
Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_object_fit_2026-06-27.md`:
implemented CSS is `133/133`, full CSS is `133/394`, full CSS unrendered is
`261`, and unsupported inventory ownership is `268`. This is a completed narrow
web-renderer slice, not completion evidence for full CSS or native platform
capture lanes.

WO-5 status: refreshed non-RenderDoc Linux evidence is passing in
`doc/09_report/gui_web_2d_linux_vulkan_refresh_2026-06-27.md`. A fresh
RenderDoc host check is recorded in
`doc/09_report/gui_web_2d_linux_renderdoc_host_blocker_2026-06-27.md`; this
host has hardware Vulkan, Chrome, and Electron available, and the Linux host
passes browser Vulkan backing, direct Electron/Chrome/Simple ARGB comparison,
Simple Vulkan backend proof, pairwise pixel comparison, Web WM modern shell
evidence, and retained 4K/8K perf in the current aggregate. The same fresh host
check found no `renderdoccmd`, `renderdoc`, or `qrenderdoc`, no passwordless
sudo for package installation, and no local `apt-cache policy renderdoc`
package row. Treat this session as `missing-renderdoccmd-in-search-paths` until
a prepared Ubuntu GUI host installs RenderDoc or exposes `RDOC_HOME`.

If `RDOC_HOME`, `renderdoccmd`, `renderdoc`, or `qrenderdoc` becomes available
on a prepared host, restart the Linux Vulkan sequence from host readiness, then
capture all required `.rdc` artifacts before strict render-log comparison. Do
not skip directly to completion from tool discovery alone.

## Linux Vulkan Sequencing

Do not run or accept strict Linux render-log comparison out of order. The Linux
platform agent must complete these gates in sequence:

1. Host readiness and browser backing:
   `scripts/setup/setup-gui-web-2d-vulkan-env.shs --check` and
   `--browser-backing`.
2. Direct Electron/Chrome/Simple ARGB comparison:
   `scripts/setup/setup-gui-web-2d-vulkan-env.shs --run`.
3. RenderDoc capture for all three lanes:
   `scripts/tool/renderdoc-evidence.shs capture-html`,
   `capture-electron-html`, and `capture-simple`.
4. Strict render-log comparison:
   `LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=1 sh scripts/check/check-linux-vulkan-render-log-compare.shs`.

If step 3 lacks valid `.rdc` files with `RDOC` magic, step 4 remains blocked.
Diagnostic runs with `LINUX_VULKAN_RENDER_LOG_REQUIRE_RDOC=0` may classify
partial state, but they are not completion evidence.

Lane B matrix note: `--browser-backing` is the focused Linux command that
satisfies the browser-backing evidence keys. `--run` is direct ARGB parity
evidence. `--renderdoc` or the explicit `scripts/tool/renderdoc-evidence.shs`
capture commands are required before any strict RenderDoc-backed comparison can
pass.

## Source Coupling Audit

Before accepting any implementation or wrapper patch from Spark, mini sidecars,
or future platform agents, Lane C must run a source-coupling review over the
diff:

- Run `sh scripts/check/check-rendering-source-coupling.shs` against the
  working diff, or set `RENDERING_SOURCE_COUPLING_REVISION=<rev>` for a
  specific jj change.
- No new raw `rt_*` calls in app, GUI, web, 2D, benchmark, or evidence-wrapper
  code unless the owning facade already exposes that operation.
- No direct backend field pokes to force pass states.
- No fixture-only runtime aliases as the default path for new capability.
- If a compatibility shim is unavoidable, it must be opt-in, documented in the
  relevant runbook, and visible in emitted evidence rows.

## Dedicated 4K/8K Retained Showcase Lane

This lane exists because the active objective explicitly requires 4K 200 FPS and
8K optimization evidence. It must remain separate from browser/RenderDoc proof:
a retained perf pass does not prove Vulkan, Metal, D3D12, or CSS compatibility.

Spark-suitable collection:

1. Inspect retained 4K/8K env rows and report paths.
2. Confirm the rows expose viewport, source revision, target FPS, observed
   frames/FPS, p50/p95 or timing log, max RSS, checksum/readback proof,
   retained render mode, redraw count, and fallback state.
3. Run `scripts/check/check-widget-showcase-4k-200fps.shs` only when the
   wrapper or showcase source changed and no current retained row exists.
4. Run `RESOLUTION=8k scripts/check/check-widget-showcase-4k-200fps.shs` only
   under the same bounded condition.

Normal-review acceptance:

- Verify `gui_showcase_4k_200fps_status=pass`,
  `gui_showcase_4k_200fps_target_fps=200`,
  `gui_showcase_4k_200fps_render_mode=retained-static-frame`,
  `gui_showcase_4k_200fps_redraw_frames=1`,
  `gui_showcase_4k_200fps_rss_status=pass`, and current source alignment.
- Verify `gui_showcase_8k_perf_status=pass`,
  `gui_showcase_8k_perf_target_fps=200`,
  `gui_showcase_8k_perf_render_mode=retained-static-frame`,
  `gui_showcase_8k_perf_redraw_frames=1`,
  `gui_showcase_8k_perf_rss_status=pass`, and current source alignment.
- Reject small viewport, software fallback, cached replay without source
  freshness, missing timing logs, missing checksum/readback proof, or missing
  RSS budget as 4K/8K completion evidence.

## Review State

- Spark Lane A: attempted twice, most recently as `Singer`; blocked by Spark
  quota until 5:04 AM and queued for restart. Attempted again in this slice as
  `Kant`; Spark quota still blocked it.
- Spark Lane B: attempted, blocked by Spark quota until 5:04 AM; queued for
  restart. Attempted again in this slice as `Pauli`; Spark quota still blocked
  it.
- Latest Spark Lane A restart: attempted as `Russell`; Spark quota blocked it
  before any findings were produced.
- Latest Spark Lane B restart: attempted as `Tesla`; Spark quota blocked it
  before any findings were produced.
- Mini fallback Lane A: completed; planning findings integrated above.
- Mini fallback Lane B: completed; wrapper/key matrix integrated above.
- Current mini fallback Lane A: completed as `McClintock`; accepted anti-
  overclaim, restart-workflow, and RenderDoc-unblock wording is integrated.
- Current mini fallback Lane B: completed as `Cicero`; it found the
  `aspect-ratio` evidence keys internally consistent and no false completion
  claim in the checked files.
- Earlier normal review Lane C: completed as `Wegener` for pre-`Russell` and
  pre-`Tesla` sidecar outputs only; accepted corrections are integrated above,
  except historical reports are not treated as current proof when a fresher
  host check disagrees.
- Current mini fallback for the Linux RenderDoc host blocker: started as
  `Rawls` after Spark quota failed; accepted corrections are integrated above.
- Current mini fallback Lane A after `Russell` quota failure: completed as
  `Feynman`; accepted stale-baseline and fresher-evidence-anchor cleanup is
  integrated in the current baseline section above. Its suggestion to update
  older broad Vulkan plans is left as a follow-up to avoid mixing another plan
  lane into the WO-11 object-fit commit.
- Current mini fallback Lane B after `Tesla` quota failure: completed as
  `Mill`; accepted command/key matrix precision is integrated in the Linux
  sequencing note above. Platform-host-only macOS/Windows capture claims remain
  unverified on this host.
- Current normal review lane: completed as `Poincare`; accepted fixes are
  integrated for WO-10/WO-11 ownership, dynamic Spark baseline wording, and
  review-scope separation. Remaining unintegrated `Feynman`/`Mill` suggestions
  remain advisory until the main agent or a later normal reviewer accepts
  specific claims.

## Hard Stop Conditions

- Do not mark the active goal complete while any required backend capture,
  platform render-log comparison, full CSS coverage, production parity, or
  RenderDoc `.rdc` gate remains incomplete.
- Do not rerun broad checks that already passed in this session.
- Stop after three verify/fix cycles for the same failing gate and record the
  blocker instead of spinning.
