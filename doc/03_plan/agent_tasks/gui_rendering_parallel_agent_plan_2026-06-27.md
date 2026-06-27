# GUI Rendering Parallel Agent Plan - 2026-06-27

## Goal

Advance the active SPipe lane for GUI hardening, web-renderer hardening, 2D
Metal/Vulkan backing, and retained 4K/8K GUI showcase performance evidence.

This plan is explicitly parallel-agent oriented. Spark sidecars may discover
gaps or draft small isolated patches, but Spark output is not accepted as done
until reviewed by the main agent or a normal/high-capability review agent.
If Spark quota is unavailable, use mini fallback sidecars for the same lane and
record that the fallback output is advisory under the same review gate.

## Current Baseline

- `main` includes `ea1b096a618c test(gui): expose web wm evidence paths`.
- 4K retained widget showcase evidence is current and passing on source
  `56a1985b1d38`.
- 8K retained widget showcase evidence is current and passing on source
  `56a1985b1d38`.
- Browser Vulkan backing evidence is current and passing for Electron and
  Chrome on the Linux host.
- RenderDoc browser capture remains blocked on this host by missing
  `renderdoccmd` in the searched paths.
- Web WM modern shell evidence now emits canonical `*_path` aliases, but the
  current host still reports `simple-runtime-unavailable` / missing artifacts.

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
2. Check for overclaiming, stale evidence, missing file-status rows, and
   accidental acceptance of unavailable host states.
3. Recommend which sidecar output is safe to integrate.

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

## Hard Stop Conditions

- Do not mark the active goal complete while any required backend capture,
  platform render-log comparison, full CSS coverage, production parity, or
  RenderDoc `.rdc` gate remains incomplete.
- Do not rerun broad checks that already passed in this session.
- Stop after three verify/fix cycles for the same failing gate and record the
  blocker instead of spinning.
