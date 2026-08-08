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
  `html_css_full_rendering_goal_full_css_rendered_count=233`, and
  `html_css_full_rendering_goal_full_css_unrendered_count=161`.
  `aspect-ratio`, `object-fit`, `object-position`, `flex-flow`, logical
  inline/block spacing, `will-change`, `color-scheme`,
  `forced-color-adjust`, and `print-color-adjust`, `color-adjust`, `speech-rate`, `pitch`, `pitch-range`, and `volume` are completed narrow
  implemented-CSS slices.

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
- 2026-06-28 fallback fan-out:
  - `Helmholtz` (`gpt-5.3-codex-spark` explorer): Lane A SSpec/perf audit;
    failed at the Spark usage-limit gate before producing findings.
  - `Erdos` (`gpt-5.3-codex-spark` explorer): Lane B platform plan/doc audit;
    failed at the Spark usage-limit gate before producing findings. This is a
    new quota-failed Spark attempt, separate from the earlier mini fallback
    named `Erdos`.
  - `Euler` (`gpt-5.4-mini` explorer): replacement Lane A SSpec/perf audit
    after Spark quota failure.
  - `Darwin` (`gpt-5.4-mini` explorer): replacement Lane B platform plan/doc
    audit after Spark quota failure.
  - `Boyle` (`gpt-5.5` explorer): higher-model review of the sidecar plan,
    overclaiming risks, and commit/push readiness gates.
    `Boyle` completed with `WARN`: the split is valid only as a headless
    preparation plan. This host can claim `prepared-not-verified`, not full
    rendering/perf completion. Remaining live gates still require Linux Vulkan
    `.rdc` evidence, macOS Metal render-log/GPU capture evidence, Windows
    D3D12/PIX evidence, iOS/Android live renderer proof, full CSS closure, and
    current-source retained 4K/8K aggregate validation.
- 2026-06-28 review refresh:
  - `Rawls` and `Euclid` (`gpt-5.3-codex-spark` explorers): requested Spark
    review lanes for SSpec/manual placeholder audit and report overclaim audit;
    both failed at the Spark quota gate before producing findings.
  - `Mendel` (`gpt-5.4-mini` explorer): replacement sidecar after Spark quota
    failure; found no blockers in the focused SSpec/manual audit and confirmed
    the checked completion criteria remain `prepared-not-verified` on this
    headless host.
  - `Dalton` (`gpt-5.5` explorer): higher-model preparedness review completed
    with `WARN`. The lane remains honest as `prepared-not-verified`, but
    documentation needed bounded clarity fixes for historical Linux evidence,
    historical mobile retained evidence, and macOS/Windows producer handoff.
    Those fixes were applied in `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md`,
    `doc/07_guide/platform/mobile/tauri_mobile_guide.md`, and
    `doc/07_guide/tooling/renderdoc_capture_infra.md`.
  - Mobile artifact gate hardening completed as headless-safe test-infra work:
    `test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl`
    now requires Android foreground markers, distinct render-log and dev-log
    sources, MDI `eventSequence` proof, and stricter row-mismatch ordering.
    Focused evidence passed `38 examples, 0 failures`. This is contract
    preparation only; live iOS/Android renderer completion still requires
    platform/emulator evidence from the mobile runbook.
- 2026-06-28 parallel-agent review refresh for WO-29:
  - `Beauvoir` and `Arendt` (`gpt-5.3-codex-spark` explorers): requested Spark
    sidecars for plan/report overclaim review and SSpec/checker/manual review;
    both failed at the Spark quota gate before producing findings.
  - `Kierkegaard` (`gpt-5.4-mini` explorer): replacement sidecar reviewed the
    plan/report contract and found the plan clear but report wording too easy
    to misread as final completion.
  - `Banach` (`gpt-5.4-mini` explorer): replacement sidecar reviewed SSpec,
    checker, and manual contracts; it found that required-gate checks were
    whole-file prose greps rather than explicit executable witnesses.
  - Main/high-capability review accepted both findings and integrated bounded
    fixes: headless reports now expose
    `gui_web_2d_headless_handoff_prep_completion_scope=prepared-not-verified`,
    human reports label wrapper/audit status instead of final completion, and
    the completion criteria audit requires explicit
    `completion_gate_witness:<gate>` markers for all `17` gates.
    Follow-up hardening added
    `gui_web_2d_completion_criteria_completion_scope=source-shape-only` so
    downstream automation can distinguish the criteria-shape audit from native
    host completion proof. The headless wrapper forwards that nested boundary
    as
    `gui_web_2d_headless_handoff_prep_completion_criteria_completion_scope`.
    It explicitly emits
    `gui_web_2d_headless_handoff_prep_live_completion_status=incomplete` with
    `gui_web_2d_headless_handoff_prep_live_completion_reason=remaining-live-gates-unverified`,
    so wrapper `pass` cannot be mistaken for live goal completion.
    It also emits
    `gui_web_2d_headless_handoff_prep_remaining_live_completion_gate_count=9`
    and a stable remaining-gate list for Linux Vulkan/RenderDoc, macOS
    Metal/Xcode GPU Capture, Windows D3D12/PIX, iOS Tauri/WKWebView Metal,
    Android Tauri/WebView Vulkan, retained 4K/8K current-source evidence, full
    HTML/CSS, production GUI/Web parity, and cross-platform freshness. The
    wrapper derives the count from the pipe-separated list so future gate
    additions cannot leave a stale numeric count. It also emits
    `gui_web_2d_headless_handoff_prep_remaining_live_completion_hosts` with
    one host/platform owner per remaining gate and fails with
    `remaining-live-host-count-mismatch` if the host map count diverges.
    It also emits
    `gui_web_2d_headless_handoff_prep_remaining_live_completion_runbooks` with
    one platform/runbook mapping per remaining gate and fails with
    `remaining-live-runbook-count-mismatch` if the map count diverges.
    This remains source-level handoff preparation only.

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
- Mobile parity gate: `scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`
- Headless handoff prep gate:
  `scripts/check/check-gui-web-2d-headless-handoff-prep.shs`
- Executable completion checklist:
  `test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl`
- Five-platform handoff contract:
  `test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl`
- Headless handoff prep wrapper spec:
  `test/03_system/check/gui_web_2d_headless_handoff_prep_spec.spl`
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

## Handoff Control Block

This block is the machine-checkable summary for future agents.

- Spark sidecar lanes: `WO-1` evidence gap scan, `WO-2` wrapper/key matrix,
  and `WO-3` sidecar review.
- Normal/high-model review gate: `WO-3` must approve sidecar findings before
  any integration claim; Spark or mini fallback output stays advisory until
  that review completes.
- Merge owner: `WO-4` main agent integration owns the merge path and is the
  only lane that may integrate reviewed changes.
- Review evidence required: current file paths, exact evidence keys, relevant
  command output or report IDs, and reviewer findings tied to the current
  source revision.
- Non-completion criteria for live platform gates: do not mark the goal done
  while any of these remain unverified on the correct native host or device:
  Linux Vulkan RenderDoc, macOS Metal, Windows D3D12, iOS Tauri/WKWebView
  Metal, Android Tauri/WebView Vulkan, retained 4K/8K perf freshness, full
  HTML/CSS coverage, or production GUI/Web parity. Cached screenshots, stale
  reports, or headless preparation alone are not completion evidence.

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
   D3D12/DXGI/PIX verification lanes.
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
  PIX or equivalent GPU-debugger capture evidence, and strict D3D12 render-log
  comparison.

Host-preparable here:

- Runbook text, evidence schema, Linux Vulkan readiness checks, browser-backing
  checks, capture plumbing, and Linux aggregate/render-log verification.

Requires another GUI platform:

- macOS Metal proof on a real Darwin host with Metal tooling.
- Windows D3D12 proof on a real Windows host with native capture tools and PIX
  or equivalent GPU-debugger evidence.

Platform acceptance keys:

- Linux: `gui_web_2d_vulkan_browser_backing_status=pass`,
  `gui_web_2d_vulkan_electron_browser_backing_status=pass`,
  `gui_web_2d_vulkan_chrome_browser_backing_status=pass`,
  `gui_web_2d_vulkan_simple_backend_status=pass`,
  `linux_vulkan_render_log_compare_status=pass`,
  `linux_vulkan_render_log_compare_required_api=vulkan`, and
  `linux_vulkan_render_log_compare_pairwise_status=pass`, plus Simple,
  Chrome, and Electron `.rdc` artifact file statuses with `RDOC` magic.
- macOS: `readback_metal_verdict=pass`,
  `macos_metal_render_log_compare_status=pass`,
  `macos_metal_render_log_compare_required_api=metal`,
  `macos_metal_render_log_compare_pairwise_status=pass`, and
  `macos_metal_render_log_compare_gpu_capture_status=pass` when GPU capture is
  required, plus GPU capture artifact file status and `XCODE-GPUTRACE` magic.
- Windows: `windows_d3d12_native_readback_api=d3d12`,
  `windows_d3d12_render_log_compare_native_readback_gate_status=pass`,
  `windows_d3d12_render_log_compare_status=pass`,
  `windows_d3d12_render_log_compare_required_api=d3d12`,
  `windows_d3d12_render_log_compare_pairwise_status=pass`,
  `windows_d3d12_render_log_compare_pix_gpu_debugger_gate_status=pass`,
  `windows_d3d12_render_log_compare_pix_status=pass`,
  `windows_d3d12_render_log_compare_pix_artifact_file_status=pass`,
  `windows_d3d12_render_log_compare_pix_artifact_magic=PIX`,
  `windows_d3d12_render_log_compare_pix_artifact_file_magic=PIX`,
  `windows_d3d12_render_log_compare_gpu_debugger_status=pass`, and
  `windows_d3d12_render_log_compare_gpu_debugger_artifact_file_status=pass`.
  `gui_web_2d_directx_native_readback_gate_status=pass` is diagnostic producer
  evidence only and does not replace the D3D12 API and render-log keys above.

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

## Explicit Completion Criteria

The active goal is complete only when the executable completion checklist in
`test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl` passes
without fail-fast placeholders and every passing scenario is backed by fresh
native-host evidence. The current file now uses real evidence-backed assertions
instead of `TODO(gui-web-2d-completion)` placeholders, but a headless local pass
is still only `prepared-not-verified` unless the required Linux/macOS/Windows
and mobile evidence was produced on the correct platform.

Placeholder audit refresh, 2026-06-28:
`doc/09_report/gui_web_2d_completion_criteria_placeholders_2026-06-28.md`
reports `gui_web_2d_completion_criteria_status=pass` and
`gui_web_2d_completion_criteria_todo_count=0`. The refreshed checker also
requires 17 named completion-gate witnesses, including Tauri mobile event
sequence/source identity and five-platform freshness criteria, and emits
`gui_web_2d_completion_criteria_completion_scope=source-shape-only`. This
scope is forwarded by the headless preparation wrapper as
`gui_web_2d_headless_handoff_prep_completion_criteria_completion_scope`. The
same wrapper emits
`gui_web_2d_headless_handoff_prep_live_completion_status=incomplete`,
`gui_web_2d_headless_handoff_prep_live_completion_reason=remaining-live-gates-unverified`,
`gui_web_2d_headless_handoff_prep_remaining_live_completion_gate_count=9` and
`gui_web_2d_headless_handoff_prep_remaining_live_completion_gates` for the
five platform renderer gates plus retained 4K/8K, full HTML/CSS, production
GUI/Web parity, and cross-platform freshness. The count is derived from that
list. It also emits
`gui_web_2d_headless_handoff_prep_remaining_live_completion_hosts` and a
matching count so each gate has a target host/platform owner, plus
`gui_web_2d_headless_handoff_prep_remaining_live_completion_runbooks` and a
matching count so platform agents can route each remaining gate without reading
the plan prose. It also emits
`gui_web_2d_headless_handoff_prep_remaining_live_completion_proofs` and a
matching count so each remaining gate has a concrete required-proof checklist;
the wrapper fails with `remaining-live-proof-count-mismatch` if that proof map
drifts from the gate list. It rejects empty or malformed map values with
`remaining-live-host-value-missing`, `remaining-live-runbook-value-missing`, or
`remaining-live-proof-value-missing`. It also emits
`gui_web_2d_headless_handoff_prep_remaining_live_completion_matrix` and a
matching count so reviewers can verify each gate, host, runbook, and proof row
without reconstructing rows from separate pipe-delimited maps; the matrix uses
`gate:host=<host>,runbook=<runbook>,proof=<proof>` rows. The wrapper also
derives gate IDs from the host, runbook, and proof maps and exposes
`gui_web_2d_headless_handoff_prep_map_gate_alignment_status`; it fails with a
specific `remaining-live-*-gate-id-mismatch` reason if any map's gate IDs differ
from the remaining gate list. It also emits
`gui_web_2d_headless_handoff_prep_gate_uniqueness_status` and fails with
`remaining-live-gate-duplicate` if the remaining gate list repeats a gate ID,
and `remaining-live-gate-value-missing` if the primary remaining gate list has
an empty gate ID.
`scripts/check/check-gui-web-2d-headless-handoff-negative-selftest.shs` runs
the wrapper in contract-selftest mode and expects duplicate-gate,
empty primary gate, host/runbook/proof count mismatch, host/runbook/proof empty
or malformed value, and host/runbook/proof gate-ID mismatch failures without
invoking nested Simple tests. The normal headless wrapper consumes that selftest
and reports
`gui_web_2d_headless_handoff_prep_negative_selftest_status=pass` plus the
case list before it reports wrapper `pass`; it fails with
`negative-selftest-case-mismatch` if the actual case list differs from
`duplicate-gate|gate-value|host-count|runbook-count|proof-count|host-value|runbook-value|proof-value|host-format|runbook-format|proof-format|host-gate-id|runbook-gate-id|proof-gate-id`
and with `negative-selftest-case-status-mismatch` if any expected case is not
reported as `case:pass`.
This closes only the source-level criteria-shape guard; it does not close
native RenderDoc, Metal, D3D12/PIX, mobile, full CSS, or production parity
gates.

Each scenario maps to one completion gate:

| Gate | Required proof | Host owner | Current state |
| --- | --- | --- | --- |
| Linux Vulkan RenderDoc | Chrome, Electron, and Simple Vulkan backing; nonblank pairwise ARGB equivalence; strict Linux render-log compare; `.rdc` artifacts with `RDOC` magic for Chrome, Electron, and Simple | Prepared Ubuntu GUI host | Blocked here by missing RenderDoc command |
| macOS Metal | Native Metal readback; browser/gui backing; pairwise equivalence; macOS render-log compare; Xcode GPU Capture proof when required | Darwin GUI host | Not run on this Linux host |
| Windows D3D12 | Native D3D12/DXGI readback; D3D12-backed Chrome/Electron/Simple browser/gui backing; pairwise ARGB equivalence; D3D12 render-log compare; strict `WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1`; verified PIX artifact file/status/magic or equivalent GPU-debugger artifact files as required by the strict wrapper | Windows GUI host | Not run on this Linux host |
| iOS Tauri/WKWebView Metal | Fresh simulator or device WKWebView + CAMetalLayer/Metal evidence; live screenshot PNG artifact checks; `ios_mdi_proof.validation.env`; coherent render-log source file/size identity; `[tauri-shell] render, html_len=` marker; production `device_readback` evidence | macOS/iOS host or simulator agent | Not run on this Linux host; source-level artifact gate only |
| Android Tauri/WebView Vulkan | Fresh emulator or device WebView + Vulkan/skiavk evidence; live screenshot PNG artifact checks; `android_mdi_proof.validation.env`; coherent render-log source file/size identity; `[tauri-shell] render, html_len=` marker; `com.simple.ui` foreground marker; production `device_readback` evidence | Android emulator/device host agent | Not run on this Linux host; source-level artifact gate only |
| 4K/8K retained perf | Current-source 4K and 8K rows at 200 FPS with viewport, p50/p95 or equivalent timing, RSS, checksum/readback, native binary provenance, retained mode, redraw count, source revision, and `fallback_state=none` | Main/perf agent | Prior retained rows pass; keep source freshness required |
| Full HTML/CSS | All HTML tags and all CSS inventory properties render; strict full CSS gate passes | Main/web-renderer agents | Incomplete: implemented CSS subset is `240/240`, full CSS inventory is `233/394` |
| Production GUI/Web parity | Same-frame backend readback, positive backend handles, matching checksums, and no CPU-mirror-only pass | Platform/main agents | Still separate from Linux direct ARGB diagnostics |
| Cross-platform freshness | Linux, macOS, Windows, iOS, Android, retained 4K/8K, full HTML/CSS, and production parity evidence reports are all fresh for the same current source revision, runtime build, browser/WebView/Electron revision, graphics SDK/driver revision, and platform runbook version | Main + platform agents | Explicit remaining handoff gate `cross-platform-freshness`; Historical evidence is retained as preparation only; final completion blocked until fresh same-revision evidence exists |
| Parallel-agent review | Spark or fallback sidecar output plus normal/high-capability review before broad findings or done marks are accepted | Main + review agent | Spark may be quota-blocked; fallback output remains advisory until reviewed |

Do not mark the overall goal done from a subset pass. A narrow CSS slice,
browser Vulkan backing row, retained 8K row, or diagnostic render-log row can
close only its own work order.

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
| WO-3 Sidecar review | Normal/high-capability Lane C | Not Spark: review must catch overclaiming | `scripts/check/check-gui-web-2d-parallel-agent-review-evidence.shs`, `test/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.spl`, mirrored manual only | Findings accept/reject each sidecar claim, Spark quota failures stay attempts only, fallback sidecars stay advisory until reviewed, and the checker fails closed when the plan is missing |
| WO-4 Plan/doc integration | Main agent | Not delegated | `doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md` and directly referenced guides only | Baseline names current commit, Spark status, review gates, and next host lanes |
| WO-5 Linux Vulkan host execution | Future platform agent on prepared Ubuntu GUI host | Medium: Spark may run readiness probes only under supervision | Evidence dirs and reports only | Browser backing and direct ARGB pairwise diff pass first; strict Linux render-log compare remains blocked until Chrome/Electron/Simple RenderDoc `.rdc` artifacts have `RDOC` magic |
| WO-6 macOS Metal host execution | Future Darwin agent | Medium: Spark may collect logs; normal review required | Evidence dirs and reports only | Native Metal readback, GPU capture if required, and macOS render-log compare pass |
| WO-7 Windows D3D12 host execution | Future Windows agent | Low/medium: Spark can collect command output; normal review required | Evidence dirs and reports only | Native D3D12/DXGI readback, `windows_d3d12_native_readback_api=d3d12`, D3D12-backed Chrome/Electron/Simple pairwise ARGB, strict `WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1`, PIX file/status/magic or equivalent GPU-debugger artifact proof, and Windows render-log compare pass; DirectX/D3D11 producer diagnostics are not completion proof |
| WO-8 4K/8K perf freshness | Main or supervised perf sidecar | Medium: Spark can check retained rows; normal review required for perf claims | Reports/metrics only | Retained rows include viewport, source revision, timing, RSS, checksum/readback, and fallback state |
| WO-9 Stale planning cleanup | Spark scan followed by normal review | High for discovery, review required for edits | `doc/03_plan/agent_tasks/gui_web_host_gpu_queue_readback_spark_tasks.md`, `doc/03_plan/agent_tasks/gui_web_gpu_host_platform_matrix.md`, and directly referenced stale plan docs | Older queue/readback and platform-matrix docs either point to current aggregate/runbook evidence or are explicitly marked historical/superseded |
| WO-10 CSS aspect-ratio slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, focused unit/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `132/132`, and no full-CSS/native-platform completion is claimed |
| WO-11 CSS object-fit slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, Electron bitmap evidence fixture, focused unit/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `133/133`, and no full-CSS/native-platform completion is claimed |
| WO-12 Spark restart queue | Main agent or future orchestrator | High: same read-only prompts after quota recovers | None | New Spark outputs are explicitly compared against `Feynman`/`Mill` fallback results and accepted only after `Poincare`-style normal review |
| WO-13 CSS object-position slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, Electron bitmap evidence fixture, focused unit/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `134/134`, and no full-CSS/native-platform completion is claimed |
| WO-14 Aggregate current-evidence autodiscovery | Main agent | Low: Spark may inspect output only | Aggregate checker, focused autodiscovery SSpec/manual doc | Default aggregate discovers current 4K, 8K, browser-backing, and direct ARGB evidence rows without explicit env overrides; blocker count drops from 16 to 10 on this host |
| WO-15 CSS flex-flow slice | Main agent | Low: Spark may only inspect evidence after implementation | CSS traceability wrapper, focused renderer/inventory/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `135/135`, and no full-CSS/native-platform completion is claimed |
| WO-16 CSS logical inline spacing slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, Electron bitmap evidence fixture, focused renderer/inventory/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `141/141`, and no full-CSS/native-platform completion is claimed |
| WO-17 Goal completion checklist SSpec | Main agent defines, Spark/fallback may inspect, normal/high-capability agent reviews | High for read-only review, low for source edits | `test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl`, generated/manual doc, this plan | The SSpec lists all final gates as evidence-backed scenario helpers; goal completion requires current native-host evidence for every assertion, not just a headless source-level pass |
| WO-18 CSS logical block spacing slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, Electron bitmap evidence fixture, focused renderer/inventory/system specs, generated docs, report | At slice completion, focused renderer spec passed, full CSS gate reported implemented CSS `147/147`, and no full-CSS/native-platform completion was claimed |
| WO-19 CSS logical sizing slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, Electron bitmap evidence fixture, focused renderer/inventory/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `153/153`, and no full-CSS/native-platform completion is claimed |
| WO-20 CSS logical inset slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, Electron bitmap evidence fixture, focused renderer/inventory/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `160/160`, and no full-CSS/native-platform completion is claimed |
| WO-21 CSS logical border slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, Electron bitmap evidence fixture, focused renderer/inventory/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `184/184`, and no full-CSS/native-platform completion is claimed |
| WO-22 CSS logical border radius slice | Main agent | Low: Spark may only inspect evidence after implementation | Renderer, CSS traceability wrapper, Electron bitmap evidence fixture, focused renderer/inventory/system specs, generated docs, report | Focused renderer spec passes, full CSS gate reports implemented CSS `188/188`, and no full-CSS/native-platform completion is claimed |
| WO-23 CSS will-change metadata slice | Main agent | Low: Spark/fallback may inspect evidence after implementation | CSS support inventory, Electron bitmap evidence fixture, focused inventory/system specs, generated docs, report | Focused specs pass, full CSS gate reports implemented CSS `232/232`, and no full-CSS/native-platform completion is claimed |
| WO-24 CSS color-scheme metadata slice | Main agent | Low: Spark/fallback may inspect evidence after implementation | CSS support inventory, Electron bitmap evidence fixture, focused inventory/system specs, generated docs, report | Focused specs pass, full CSS gate reports implemented CSS `233/233`, and no full-CSS/native-platform completion is claimed |
| WO-25 CSS forced-color-adjust metadata slice | Main agent | Low: Spark/fallback may inspect evidence after implementation | CSS support inventory, Electron bitmap evidence fixture, focused inventory/system specs, generated docs, report | Focused specs pass, full CSS gate reports implemented CSS `234/234`, and no full-CSS/native-platform completion is claimed |
| WO-26 CSS print-color-adjust metadata slice | Main agent | Low: Spark/fallback may inspect evidence after implementation | CSS support inventory, Electron bitmap evidence fixture, focused inventory/system specs, generated docs, report | Focused specs pass, full CSS gate reports implemented CSS `235/235`, and no full-CSS/native-platform completion is claimed |
| WO-27 CSS adjust/aural metadata slice | Main agent | Low: Spark/fallback may inspect evidence after implementation | CSS support inventory, Electron bitmap evidence fixture, focused inventory/system specs, generated docs, report | Focused specs pass, full CSS gate reports implemented CSS `240/240`, and no full-CSS/native-platform completion is claimed |
| WO-28 Tauri mobile artifact gate hardening | Main agent, Spark fallback may inspect, high-model reviewer validates claim boundaries | Medium for read-only review, low for edits | Mobile artifact gate SSpec/manual doc and bug report only | Focused SSpec passes `38/38`; Android foreground marker, distinct render-log/dev-log sources, MDI `eventSequence`, and first-failure row-mismatch assertions are part of the contract; final completion still requires live iOS and Android host/emulator evidence |
| WO-29 Five-platform handoff contract | Main agent owns, Spark/fallback may inspect after source freeze, high-model reviewer validates no overclaim | High for read-only review, low for edits | `test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl`, `test/03_system/check/gui_web_2d_headless_handoff_prep_spec.spl`, `scripts/check/check-gui-web-2d-headless-handoff-negative-selftest.shs`, mirrored manuals, completion-gate checker, this plan | Focused SSpecs pass `3/3` and `4/4`; required-gate checker reports `17` explicit `completion_gate_witness:<gate>` markers and includes `five-platform-handoff-spec`; negative selftest passes duplicate-gate, empty primary gate, host/runbook/proof count mismatch, host/runbook/proof empty/malformed-value, and host/runbook/proof gate-ID mismatch failure cases; headless wrapper consumes that negative selftest, checks the exact expected `duplicate-gate|gate-value|host-count|runbook-count|proof-count|host-value|runbook-value|proof-value|host-format|runbook-format|proof-format|host-gate-id|runbook-gate-id|proof-gate-id` case list and per-case `case:pass` status set, and reports it as pass, reports pass with `completion_scope=prepared-not-verified`, emits live completion `incomplete`, forwards criteria scope/counts, lists `9` unique remaining live completion gates including `cross-platform-freshness`, maps each gate to a host/platform owner, runbook, and required-proof checklist, emits `gui_web_2d_headless_handoff_prep_remaining_live_completion_matrix`, reports zero primary gate and host/runbook/proof bad values, and verifies exact map gate-ID alignment while preserving the no-live-evidence boundary; this closes only handoff wiring |
| WO-30 Retained 4K/8K current-source freshness contract | Main agent owns, Spark/fallback may inspect after source freeze, high-model reviewer validates no perf overclaim | Medium for read-only review, low for edits | `scripts/check/check-gui-web-2d-headless-handoff-prep.shs`, `scripts/check/check-widget-showcase-4k-200fps.shs`, `test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl`, this plan | Handoff wrapper keeps `retained-4k-8k-current-source` as an explicit remaining live gate mapped to `perf-capable-native-gui-host`, runbook `scripts/check/check-widget-showcase-4k-200fps.shs`, and proof checklist `4k-200fps+8k-200fps+source-revision+rss+checksum+fallback-none`; this converts retained perf from report-only context into a machine-checked handoff row and still requires fresh native GUI host evidence before any 4K/8K completion claim |
| WO-31 Full HTML/CSS final inventory contract | Main/web-renderer agents own, Spark/fallback may inspect inventory diffs after source freeze, high-model reviewer validates no coverage overclaim | Medium for read-only review, low for edits | `scripts/check/check-gui-web-2d-headless-handoff-prep.shs`, `scripts/check/check-html-css-full-rendering-goal-status.shs`, `test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl`, this plan | Handoff wrapper keeps `full-html-css` as an explicit remaining live gate mapped to `headless-or-gui-source-plus-renderer-evidence`, runbook `scripts/check/check-html-css-full-rendering-goal-status.shs`, and proof checklist `all-html+all-css-inventory+zero-unrendered+animation-css`; completion requires the full inventory gate to prove all HTML/CSS inventory rows render with zero unrendered properties, not just the current implemented subset |
| WO-32 Production GUI/Web parity final evidence contract | Platform/main agents own, Spark/fallback may inspect evidence rows after source freeze, high-model reviewer validates no parity overclaim | Medium for read-only review, low for edits | `scripts/check/check-gui-web-2d-headless-handoff-prep.shs`, `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`, `test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl`, this plan | Handoff wrapper keeps `production-gui-web-parity` as an explicit remaining live gate mapped to `gui-host-with-tauri-chrome-backend-readback`, runbook `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`, and proof checklist `tauri-chrome-captures+device-readback+event-routing+checksum-match+no-tolerance`; completion requires live Tauri/Chrome captures, same-frame device readback, event routing proof, and strict checksum parity with no CPU-mirror-only pass |
| WO-33 Cross-platform freshness final evidence contract | Main + platform agents own, Spark/fallback may inspect report metadata after source freeze, high-model reviewer validates no stale-evidence overclaim | Medium for read-only review, low for edits | `scripts/check/check-gui-web-2d-headless-handoff-prep.shs`, `test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl`, this plan | Handoff wrapper keeps `cross-platform-freshness` as an explicit remaining live gate mapped to `main-plus-platform-freshness-review`, runbook `doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md+scripts/check/check-gui-web-2d-headless-handoff-prep.shs`, and proof checklist `same-source-revision+runtime-build+browser-webview-electron-revision+graphics-sdk-driver+runbook-version`; completion requires all platform, retained perf, full HTML/CSS, and production parity evidence to share the same current source and toolchain context |

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

WO-13 status, 2026-06-27: `object-position` moved into implemented Simple Web
CSS with focused contained image-placeholder pixel coverage and full-goal status
coverage. Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_object_position_2026-06-27.md`:
implemented CSS is `134/134`, full CSS is `134/394`, full CSS unrendered is
`260`, and unsupported inventory ownership is `267`. This is a completed narrow
web-renderer slice, not completion evidence for full CSS or native platform
capture lanes.

WO-14 status, 2026-06-27: the aggregate checker now auto-discovers current
refresh evidence under `build/widget-showcase-4k-200fps-current-*`,
`build/widget-showcase-8k-perf-current-*`,
`build/gui-web-2d-vulkan-env-check-current*`,
`build/gui-web-2d-vulkan-env-run-current*`, and
`build/gui-web-2d-vulkan-env-browser-backing-current*` when explicit env
overrides are absent. Focused verification:
`test/03_system/check/gui_renderdoc_aggregate_autodiscovery_spec.spl` passes.
A quiet default aggregate run with current-source checking reports 4K `pass`,
8K `pass`, browser backing `pass`, and direct ARGB pixel comparison `pass`.
The 2026-06-28 focused aggregate refresh reports
`blocked_completion_gate_count=8`; Linux render-log comparison is narrowed to
`renderdoc-chrome-rdc` and `renderdoc-electron-rdc` because Simple RenderDoc,
browser backing, pairwise ARGB comparison, and ARGB source gates pass. Remaining
blockers are still browser/Electron RenderDoc `.rdc`, platform render-log
comparison across Linux/macOS/Windows, production parity/font/Metal, and full
CSS completion. This aggregate blocker count is intentionally separate from
the headless handoff matrix count of `9`; the handoff matrix includes
`cross-platform-freshness` as a routing/completion-readiness gate, while the
aggregate blocker count is the current evidence wrapper's blocked proof list.
Current evidence summaries:
`doc/09_report/linux_vulkan_render_log_compare_focused_2026-06-28.md` and
`doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-28.md`.

WO-15 status, 2026-06-27: `flex-flow` moved into implemented Simple Web CSS
as a parser-expanded shorthand that feeds the existing `flex-direction` and
`flex-wrap` renderer paths. Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_flex_flow_2026-06-27.md`:
implemented CSS is `135/135`, full CSS is `135/394`, full CSS unrendered is
`259`, and unsupported inventory ownership is `266`. This is a completed
narrow web-renderer slice, not completion evidence for full CSS or native
platform capture lanes.

WO-16 status, 2026-06-27: `margin-inline`, `margin-inline-start`,
`margin-inline-end`, `padding-inline`, `padding-inline-start`, and
`padding-inline-end` moved into implemented Simple Web CSS for the default
horizontal layout path. Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_logical_inline_spacing_2026-06-27.md`:
implemented CSS is `141/141`, full CSS is `141/394`, full CSS unrendered is
`253`, and unsupported inventory ownership is `260`. This is a completed
narrow web-renderer slice, not completion evidence for writing-mode/RTL logical
mapping, full CSS, RenderDoc, Metal, or D3D12 lanes.

WO-17 status, 2026-06-27: the completion checklist SSpec exists with one
fail-fast helper per final gate. It is expected to fail until platform agents
replace placeholders with assertions over fresh evidence. Generated/manual
SSpec output should be used as the operator-facing checklist for future
Linux/macOS/Windows/perf/full-CSS completion reviews.

WO-18 status, 2026-06-27: `margin-block`, `margin-block-start`,
`margin-block-end`, `padding-block`, `padding-block-start`, and
`padding-block-end` moved into implemented Simple Web CSS for the default
horizontal writing-mode path. Slice evidence at completion is recorded in
`doc/09_report/html_css_full_rendering_goal_status_logical_block_spacing_2026-06-27.md`:
implemented CSS is `147/147`, full CSS is `147/394`, full CSS unrendered is
`247`, and unsupported inventory ownership is `254`. This is a completed
narrow web-renderer slice, not completion evidence for vertical writing-mode
remapping, full CSS, RenderDoc, Metal, or D3D12 lanes.

WO-19 status, 2026-06-27: `inline-size`, `block-size`,
`min-inline-size`, `max-inline-size`, `min-block-size`, and
`max-block-size` moved into implemented Simple Web CSS for the default
horizontal writing-mode path. Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_logical_sizing_2026-06-27.md`:
implemented CSS is `153/153`, full CSS is `153/394`, full CSS unrendered is
`241`, and unsupported inventory ownership is `248`. This is a completed
narrow web-renderer slice, not completion evidence for vertical writing-mode
remapping, full CSS, RenderDoc, Metal, or D3D12 lanes.

WO-20 status, 2026-06-27: `inset`, `inset-block`,
`inset-block-start`, `inset-block-end`, `inset-inline`,
`inset-inline-start`, and `inset-inline-end` moved into implemented Simple Web
CSS for the default horizontal writing-mode path. Current evidence is recorded
in
`doc/09_report/html_css_full_rendering_goal_status_logical_inset_2026-06-27.md`:
implemented CSS is `160/160`, full CSS is `160/394`, full CSS unrendered is
`234`, and unsupported inventory ownership is `241`. This is a completed
narrow web-renderer slice, not completion evidence for vertical writing-mode
remapping, full CSS, RenderDoc, Metal, or D3D12 lanes.

WO-21 status, 2026-06-27: logical border block/inline shorthand and
start/end width, color, and style properties moved into implemented Simple Web
CSS for the default horizontal writing-mode path. Current evidence is recorded
in
`doc/09_report/html_css_full_rendering_goal_status_logical_border_2026-06-27.md`:
implemented CSS is `184/184`, full CSS is `184/394`, full CSS unrendered is
`210`, and unsupported inventory ownership is `217`. This is a completed
narrow web-renderer slice, not completion evidence for vertical writing-mode
remapping, full CSS, RenderDoc, Metal, or D3D12 lanes.

WO-22 status, 2026-06-27: `border-start-start-radius`,
`border-start-end-radius`, `border-end-start-radius`, and
`border-end-end-radius` moved into implemented Simple Web CSS for the default
horizontal writing-mode path. Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_logical_radius_2026-06-27.md`:
implemented CSS is `188/188`, full CSS is `188/394`, full CSS unrendered is
`206`, and unsupported inventory ownership is `213`. This is a completed
narrow web-renderer slice, not completion evidence for vertical writing-mode
remapping, full CSS, RenderDoc, Metal, or D3D12 lanes.

WO-23 status, 2026-06-28: `will-change` moved into implemented Simple Web CSS
as renderer-recognized metadata/hint. It is accepted by the CSS support
inventory and covered by the transform/animation fixture without changing
layout or pixel semantics. Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_will_change_2026-06-28.md`:
implemented CSS is `232/232`, full CSS is `232/394`, full CSS unrendered is
`162`, and unsupported inventory ownership is `169`. This is a completed narrow
web-renderer slice, not completion evidence for full CSS, RenderDoc, Metal, or
D3D12 lanes. The direct unit inventory spec and the broader full-status SSpec
both pass. The full-status SSpec runs the expensive wrapper once and checks the
strict-mode fail-closed path as a source contract to avoid test-daemon timeout.

WO-24 status, 2026-06-28: `color-scheme` moved into implemented Simple Web CSS
as renderer-recognized metadata/hint. It is accepted by the CSS support
inventory and covered by the transform/animation fixture without changing
layout or pixel semantics. Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_color_scheme_2026-06-28.md`:
implemented CSS is `233/233`, full CSS is `233/394`, full CSS unrendered is
`161`, and unsupported inventory ownership is `168`. This is a completed narrow
web-renderer slice, not completion evidence for full CSS, RenderDoc, Metal, or
D3D12 lanes. The full-status SSpec now uses a checked evidence fixture and
wrapper source-contract checks so it stays fast in the test daemon while the
shell wrapper report remains the authoritative generated evidence.

WO-25 status, 2026-06-28: `forced-color-adjust` moved into implemented Simple
Web CSS as renderer-recognized metadata/hint. It is accepted by the CSS support
inventory and covered by the transform/animation fixture without changing
layout or pixel semantics. Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_forced_color_adjust_2026-06-28.md`:
implemented CSS is `234/234`, full CSS is `234/394`, full CSS unrendered is
`160`, and unsupported inventory ownership is `167`. This is a completed narrow
web-renderer slice, not completion evidence for full CSS, RenderDoc, Metal, or
D3D12 lanes.

WO-26 status, 2026-06-28: `print-color-adjust` moved into implemented Simple
Web CSS as renderer-recognized metadata/hint. It is accepted by the CSS support
inventory and covered by the transform/animation fixture without changing
layout or pixel semantics. Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_print_color_adjust_2026-06-28.md`:
implemented CSS is `235/235`, full CSS is `235/394`, full CSS unrendered is
`159`, and unsupported inventory ownership is `166`. This is a completed narrow
web-renderer slice, not completion evidence for full CSS, RenderDoc, Metal, or
D3D12 lanes.

WO-27 status, 2026-06-28: `color-adjust`, `speech-rate`, `pitch`,
`pitch-range`, and `volume` moved into implemented Simple Web CSS as
renderer-recognized adjustment/aural metadata. They are accepted by the CSS
support inventory and covered by the transform/animation fixture without
changing visual layout or pixel semantics. Current evidence is recorded in
`doc/09_report/html_css_full_rendering_goal_status_adjust_aural_metadata_2026-06-28.md`:
implemented CSS is `240/240`, full CSS inventory is `233/394`, full CSS
unrendered is `161`, and unsupported inventory ownership is `161`. This is a completed narrow
web-renderer slice, not completion evidence for full CSS, RenderDoc, Metal, or
D3D12 lanes.

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
  `gui_showcase_4k_200fps_rss_status=pass`,
  `gui_showcase_4k_200fps_fallback_state=none`, native binary provenance, and
  current source alignment.
- Verify `gui_showcase_8k_perf_status=pass`,
  `gui_showcase_8k_perf_target_fps=200`,
  `gui_showcase_8k_perf_render_mode=retained-static-frame`,
  `gui_showcase_8k_perf_redraw_frames=1`,
  `gui_showcase_8k_perf_rss_status=pass`,
  `gui_showcase_8k_perf_fallback_state=none`, native binary provenance, and
  current source alignment.
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
- 2026-06-28 Spark Lane A restart: attempted as `Helmholtz`; Spark quota
  blocked it before any findings were produced.
- 2026-06-28 Spark Lane B restart: attempted as `Erdos`; Spark quota blocked it
  before any findings were produced. This name is ambiguous with an earlier
  mini fallback, so status must be read from this dated bullet.
- 2026-06-28 mini fallback Lane A: started as `Euler` to audit the SSpec/manual
  doc and retained 4K/8K evidence criteria after the Spark quota failure.
- 2026-06-28 mini fallback Lane B: started as `Darwin` to audit platform
  plan/runbook completion criteria after the Spark quota failure.
- 2026-06-28 higher-model review lane: started as `Boyle` (`gpt-5.5`) to review
  the sidecar split, anti-overclaim rules, and focused commit/push gates before
  accepting broad findings or done marks.
- 2026-06-28 higher-model review result: `Boyle` returned `WARN`. Accepted
  boundary: this headless host may only mark the lane `prepared-not-verified`;
  any stronger done claim needs live platform evidence for Linux Vulkan,
  macOS Metal, Windows D3D12, iOS, Android, full CSS, and retained 4K/8K
  current-source aggregate validation.
- 2026-06-28 mini fallback Lane A result: `Euler` found the retained 4K/8K
  criteria mechanically complete and identified a Linux Vulkan RenderDoc gap;
  accepted fix: assert aggregate env-file status, RenderDoc gate status, and
  per-surface RenderDoc status/reason fields in the completion SSpec.
- 2026-06-28 mini fallback Lane B result: `Darwin` confirmed the headless-host
  criterion is explicit, but flagged fragmented/stale guide and report pages.
  Accepted as follow-up planning only for
  `doc/07_guide/tooling/renderdoc_capture_infra.md`,
  `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md`, and stale `doc/09_report`
  snapshots; do not treat those stale pages as current proof.
- 2026-06-28 source-coupling guard result: the first
  `sh scripts/check/check-rendering-source-coupling.shs` launch failed before
  checking because jj reported a stale working copy. After
  `jj workspace update-stale` refreshed working-copy metadata, the same guard
  returned `STATUS: PASS rendering-source-coupling`. Treat this as source-
  coupling evidence only: the current rendering-scoped diff does not introduce
  new raw `rt_*` shortcuts, direct backend proof/status pokes, or forced pass
  shortcuts.
- 2026-06-28 parallel review refresh: requested Spark sidecars could not run
  because the Spark quota was exhausted. The replacement mini sidecar found the
  plan/guide headless boundary, and the higher-model review found one required
  correction: current 4K/8K evidence is retained static alias performance with
  source freshness and no interpreter fallback, not non-software GPU throughput
  or dynamic non-cached 8K rendering. Completion criteria and this plan now
  require native-host evidence, byte-level capture artifacts, and explicit
  headless `prepared-not-verified` wording before any broad done claim.
- 2026-06-28 completion-cache hardening: final completion SSpec runs now set
  `GUI_RENDERDOC_AGGREGATE_DISABLE_DEFAULT_STATIC_CACHE=1` and use only a
  per-run aggregate static cache. This prevents native-host completion from
  passing solely by replaying stale shared nested-gate evidence; platform lanes
  still need fresh host artifacts and backend proof.
- 2026-06-28 cache-mode SSpec refresh: the aggregate wrapper now exposes
  `GUI_RENDERDOC_AGGREGATE_CACHE_CONFIG_SELFTEST=1`, and
  `test/03_system/check/gui_renderdoc_aggregate_cache_modes_spec.spl` asserts
  both halves of the cache contract: read-only seeded cache precedence for
  normal fast lanes, and disabled default shared cache with explicit per-run
  cache preservation for final completion lanes.
- 2026-06-28 RenderDoc guide refresh: `doc/07_guide/tooling/renderdoc_capture_infra.md`
  now separates fast repeated aggregate checks from final native-host
  completion mode. Final completion must disable the default shared cache, use a
  per-run aggregate cache, and avoid read-only seeded cache replay.
- 2026-06-28 platform runbook refresh: `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md`
  now shows final aggregate completion with disabled shared cache and byte-level
  `RDOC`/`PIX`/Xcode capture magic requirements, and
  `doc/07_guide/platform/mobile/tauri_mobile_guide.md` now marks retained mobile
  pass reports as non-standing completion evidence that must be refreshed on the
  target host/emulator.
- 2026-06-28 SSpec check bug recorded:
  `doc/08_tracking/bug/sspec_simple_check_describe_it_parser_2026-06-28.md`.
  Do not use `bin/simple check` as the syntax gate for `std.spec` scenario files
  in this lane; it currently rejects normal `describe`/`it` DSL syntax. Use the
  focused SSpec runner or wrapper guards instead.
- 2026-06-28 WO-29 parallel-agent refresh: Spark restart attempted as `Boole`
  with `gpt-5.3-codex-spark`, but the Spark quota blocked it before findings.
  Higher-model review completed as `Harvey` with `gpt-5.5`; accepted fixes are
  integrated in the headless handoff wrapper/report label and the five-platform
  manual summary so source-shape audits cannot be misread as live completion.
  Harvey found the 13-case negative selftest list and per-case pass set
  consistent across wrapper, SSpec expectations, and report. Final status remains
  `prepared-not-verified` with 9 live gates outstanding.
- 2026-06-28 platform evidence bundle prep: `scripts/check/check-gui-web-2d-platform-evidence-bundle.shs`
  is the non-launching rollup for the nine live gates. It consumes existing
  native render-log, Tauri mobile, retained 4K/8K, full HTML/CSS, production
  GUI/Web parity, and cross-platform freshness env files, then emits proven,
  missing, failed, and remaining gate lists. Missing envs remain incomplete and
  present bad rows remain failed; this prepares shared verification without
  claiming live platform completion on the headless host.
- 2026-06-28 platform freshness producer prep:
  `scripts/check/check-gui-web-2d-platform-freshness.shs` produces the
  `gui_web_2d_platform_freshness_*` env consumed by the bundle. It compares the
  source revision across native render-log, Tauri mobile, retained 4K, retained
  8K, full HTML/CSS, and production parity env files, then records runtime
  build, browser/WebView/Electron revision, graphics SDK/driver, and runbook
  version metadata. Missing files, missing source revisions, mismatched source
  revisions, or missing freshness metadata fail closed.
- 2026-06-28 source-revision producer prep: native RenderDoc aggregate, Tauri
  mobile parity, HTML/CSS full rendering status, and production GUI/Web parity
  wrappers now emit lane-specific source revision keys plus the shared
  `gui_web_2d_evidence_source_revision` fallback consumed by the freshness
  checker. `GUI_WEB_2D_PLATFORM_FRESHNESS_SOURCE_REVISION` can pin a final
  review window across wrappers on platform hosts.
- 2026-06-28 freshness metadata producer prep: native RenderDoc aggregate now
  emits `native_render_log_platform_matrix_runtime_build`,
  `native_render_log_platform_matrix_browser_webview_electron_revision`,
  `native_render_log_platform_matrix_graphics_sdk_driver`, and
  `native_render_log_platform_matrix_runbook_version`, plus shared
  `gui_web_2d_evidence_*` fallbacks. Final platform runs can supply the values
  through `GUI_WEB_2D_PLATFORM_FRESHNESS_RUNTIME_BUILD`,
  `GUI_WEB_2D_PLATFORM_FRESHNESS_BROWSER_WEBVIEW_ELECTRON_REVISION`,
  `GUI_WEB_2D_PLATFORM_FRESHNESS_GRAPHICS_SDK_DRIVER`, and
  `GUI_WEB_2D_PLATFORM_FRESHNESS_RUNBOOK_VERSION`.
- 2026-06-28 parallel-agent review evidence prep:
  `test/03_system/check/gui_web_2d_parallel_agent_review_evidence_spec.spl`
  now directly runs
  `scripts/check/check-gui-web-2d-parallel-agent-review-evidence.shs` and
  asserts pass evidence for Spark attempts, mini fallback sidecars,
  normal/high-capability review, accepted split boundaries, anti-overclaim
  rules, and reviewed findings. It also asserts the checker fails closed when
  the plan file is missing. This is a headless review-contract gate only; it
  does not produce live renderer, platform, or performance evidence.
- 2026-06-28 retained perf bundle precedence fix:
  `scripts/check/check-gui-web-2d-platform-evidence-bundle.shs` now classifies
  the combined `retained-4k-8k-current-source` gate as failed if either present
  retained perf row is failed, even when the companion 4K or 8K env is still
  missing. The regression is covered by
  `test/03_system/check/gui_web_2d_platform_evidence_bundle_spec.spl`. This
  prevents bad present retained perf evidence from being hidden as merely
  missing platform work.
- 2026-06-28 present-incomplete bundle evidence contract:
  `test/03_system/check/gui_web_2d_platform_evidence_bundle_spec.spl` now
  asserts that an existing platform env with a missing required lane key is
  classified as failed evidence, not as missing work. Missing means no env was
  produced; failed means a host or wrapper produced evidence too weak for final
  completion.
- 2026-06-28 freshness metadata fail-closed contract:
  `test/03_system/check/gui_web_2d_platform_freshness_spec.spl` now asserts
  that all lanes sharing the same source revision is not enough for
  cross-platform freshness. Runtime build, browser/WebView/Electron revision,
  graphics SDK/driver, and runbook version metadata must also be present, or
  freshness fails with `missing-freshness-metadata`.
- 2026-06-28 bundle freshness metadata revalidation:
  `test/03_system/check/gui_web_2d_platform_evidence_bundle_spec.spl` now
  asserts that the platform evidence bundle rejects a freshness env that says
  `status=pass` but omits required freshness metadata. A hand-edited or partial
  freshness env cannot make `cross-platform-freshness` look proven.
- 2026-06-28 bundle freshness reason revalidation:
  `scripts/check/check-gui-web-2d-platform-evidence-bundle.shs` now also
  requires `gui_web_2d_platform_freshness_reason=pass` before accepting
  `cross-platform-freshness`. A contradictory freshness env such as
  `status=pass` with `reason=source-revision-mismatch` remains failed evidence
  even if all required metadata fields are present.
- 2026-06-28 freshness cross-lane metadata consistency:
  `scripts/check/check-gui-web-2d-platform-freshness.shs` now derives run
  metadata from any lane or explicit run-level overrides, then rejects non-empty
  conflicting lane metadata with `metadata-mismatch`. Same-source evidence from
  different runtime, browser/WebView/Electron, graphics SDK/driver, or runbook
  windows cannot satisfy `cross-platform-freshness`.
- 2026-06-28 freshness metadata mismatch coverage:
  `test/03_system/check/gui_web_2d_platform_freshness_spec.spl` now covers
  mismatch diagnostics for runtime build, browser/WebView/Electron revision,
  graphics SDK/driver, and runbook version labels, so all freshness metadata
  fields have fail-closed regression coverage.
- 2026-06-28 freshness override mismatch coverage:
  `test/03_system/check/gui_web_2d_platform_freshness_spec.spl` now asserts
  that explicit run-level metadata overrides cannot hide conflicting non-empty
  metadata already present in a lane env. Operator-provided metadata is accepted
  only when the upstream evidence does not contradict it.
- 2026-06-28 freshness source override mismatch coverage:
  `test/03_system/check/gui_web_2d_platform_freshness_spec.spl` now asserts
  that an explicit `GUI_WEB_2D_PLATFORM_FRESHNESS_SOURCE_REVISION` selects the
  review window but cannot hide a lane env whose source revision is stale or
  different from that selected revision.
- 2026-06-28 freshness duplicate source key revalidation:
  `scripts/check/check-gui-web-2d-platform-freshness.shs` now rejects duplicate
  accepted source-revision keys inside each present lane env before comparing
  lane freshness. A hand-edited or concatenated env cannot hide a stale source
  line by appending a later fresh value for the same key.
- 2026-06-28 freshness source alias revalidation:
  the freshness checker now also rejects multiple accepted source-revision
  alias forms in the same lane env, such as a stale shared
  `gui_web_2d_evidence_source_revision` next to a fresh lane-specific source
  key. Alias priority cannot hide stale source evidence.
- 2026-06-28 freshness duplicate metadata key revalidation:
  `scripts/check/check-gui-web-2d-platform-freshness.shs` now rejects duplicate
  accepted runtime, browser/WebView/Electron, graphics SDK/driver, and runbook
  metadata keys inside each present lane env. A concatenated env cannot hide an
  earlier conflicting toolchain value by appending a later matching value.
- 2026-06-28 bundle optional reason revalidation:
  `scripts/check/check-gui-web-2d-platform-evidence-bundle.shs` now rejects a
  required gate status key when the sibling optional reason key is present and
  not `pass`. A lane env with `*_status=pass` and `*_reason=<failure>` cannot
  satisfy a live completion gate.
- 2026-06-28 bundle duplicate key revalidation:
  `scripts/check/check-gui-web-2d-platform-evidence-bundle.shs` now rejects
  duplicate required gate status keys, duplicate optional gate reason keys, and
  duplicate required freshness keys. A hand-edited env cannot hide a failing
  value by appending a later `pass` line.
- 2026-06-28 bundle freshness diagnostic revalidation:
  `scripts/check/check-gui-web-2d-platform-evidence-bundle.shs` now rejects a
  freshness env that says `status=pass` and `reason=pass` while carrying
  non-empty diagnostic failure lists such as duplicate source, missing source,
  mismatched metadata, or missing metadata lanes. A contradictory freshness env
  cannot satisfy `cross-platform-freshness`.
- 2026-06-28 bundle duplicate diagnostic coverage:
  `test/03_system/check/gui_web_2d_platform_evidence_bundle_spec.spl` now also
  asserts that duplicate freshness diagnostic keys fail the
  `cross-platform-freshness` gate even when the duplicated values are empty.
- 2026-06-28 headless handoff empty-gate revalidation:
  `scripts/check/check-gui-web-2d-headless-handoff-prep.shs` now reports a
  primary remaining-gate bad-value count and fails
  `remaining-live-gate-value-missing` if the remaining live gate list contains
  an empty gate ID, even when host/runbook/proof maps align with that empty key.
  The negative selftest wrapper includes the `gate-value` case so malformed
  handoff completion maps cannot hide a missing live-platform gate name.

## Remaining Headless Plan - 2026-06-29

Current headless host scope is contract preparation only. The goal is
`headless-prepared`, not live rendering completion. A headless work item is
complete only when the executable SSpec/manual pair exists, the focused SSpec
passes once on current `main@origin`, docgen reports the affected manual as
complete with zero stubs, `doc/06_spec` contains zero executable `.spl` files,
and the text states that live Vulkan, Metal, D3D12/PIX, iOS, Android, Chrome,
Electron, RenderDoc, Xcode, PIX, and 4K/8K GUI evidence are still required on
platform hosts.

Headless completion checklist for this slice:

| Headless item | Owner | Files | Acceptance |
| --- | --- | --- | --- |
| Handoff stale/missing assertion audit | Main agent, Spark/normal read-only review | `scripts/check/check-gui-web-2d-headless-handoff-prep.shs`, `test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl`, `test/03_system/check/gui_web_2d_headless_handoff_prep_spec.spl`, completion criteria SSpec, this plan | Current `main@origin` contains the wrapper/spec files; completion criteria references match existing files; stale sidecar reports are marked invalid for this checkout, not integrated blindly |
| macOS Metal positive Xcode capture contract | Main agent, Spark read-only review, normal/high review | `test/03_system/check/native_render_log_platform_matrix_contract_spec.spl`, mirrored manual | Synthetic all-platform matrix row passes with macOS `required_api=metal`, all macOS gates `pass`, `gpu_capture_artifact_file_status=pass`, and `gpu_capture_artifact_magic=XCODE-GPUTRACE`; manual states this proves contract shape only, not a real Xcode capture |
| Windows D3D12/PIX handoff wording | Main agent, Windows sidecar read-only review | This plan | Windows rows name `windows_d3d12_native_readback_api=d3d12`, D3D12-backed Chrome/Electron/Simple pairwise ARGB, strict `WINDOWS_D3D12_RENDER_LOG_REQUIRE_PIX=1`, and PIX/GPU-debugger file proof; no wording treats DirectX/D3D11 producer diagnostics as final D3D12/PIX completion |
| Android coherent render-log alias fixtures | Main agent, Android/Tauri sidecar read-only review | `test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl`, mirrored manual | Android coherent render-log source symlink and hardlink fixtures fail with `android-render-log-coherent-source-symlink` and `android-render-log-coherent-source-hardlink`, including typed file reasons; manual states this is artifact-forgery protection only |

Headless verification notes for this slice:

- `test/03_system/check/native_render_log_platform_matrix_contract_spec.spl`
  was run once on this host. The newly added macOS Xcode-capture-shaped
  positive scenario passed, but the full file still has six existing/stale
  failures in earlier matrix scenarios on current `main@origin`; treat those as
  a separate native-matrix cleanup item, not as live-platform completion.
- `test/03_system/check/tauri_mobile_renderer_parity_artifact_gate_spec.spl`
  was run once and the test daemon timed out before file completion. The new
  Android coherent-source alias scenarios remain headless-prepared and
  documented; full-file runtime verification needs either a narrower runner or
  a split/optimized artifact-gate spec before it can be a reliable green gate.
- Docgen completed for both affected SSpecs with `0` stubs, and
  `find doc/06_spec -name '*_spec.spl'` reported `0`.
- Handoff stale/missing assertion re-check on current `main@origin` found the
  headless handoff wrapper/spec files present, so earlier sidecar reports that
  those files were missing are stale for this checkout.

Parallel-agent plan:

- Spark lane A: read-only Metal matrix contract check. Output may identify
  missing assertions but cannot be accepted without main-agent verification.
- Normal lane B: read-only Windows wording/key audit. Output is accepted only
  when current file paths and exact keys still match.
- Normal lane C: read-only Android/Tauri artifact-gate audit. Output is
  accepted only if it preserves live-device overclaim boundaries.
- High-capability review lane: read-only review of the final diff before
  push. Findings must be resolved or recorded explicitly.

Remaining non-headless completion gates after this slice:

- Linux Vulkan: real Chrome/Electron/Simple Vulkan RenderDoc `.rdc` captures
  with `RDOC` magic and pairwise ARGB equivalence on an Ubuntu GUI host.
- macOS Metal: real Metal/Xcode GPU capture and Metal render-log compare on a
  Darwin GUI host.
- Windows D3D12: real D3D12/PIX or GPU-debugger capture and render-log compare
  on a Windows GUI host.
- iOS/Android: real Tauri2/WKWebView/WebView device or emulator evidence with
  coherent render-log sources and screenshots.
- Retained 4K/8K, full HTML/CSS, production GUI/Web parity, and
  cross-platform freshness must all be rerun against the same current source
  and toolchain context before overall completion.

## Hard Stop Conditions

- Do not claim stronger than `prepared-not-verified` from this headless host.
- Do not mark the active goal complete while any required backend capture,
  platform render-log comparison, full CSS coverage, production parity, or
  RenderDoc `.rdc` gate remains incomplete.
- Do not rerun broad checks that already passed in this session.
- Stop after three verify/fix cycles for the same failing gate and record the
  blocker instead of spinning.
