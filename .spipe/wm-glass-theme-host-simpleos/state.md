# Feature: WM Glass Theme on Host and SimpleOS

## Raw Request
`$sp_dev check wm on host and simple os on qemu. and fix unwired and unimpled and bug. specially simple gui and simpwl wm does not apply theme properly which created from stitch in glass theme like mac fill. research current files and git history check theme apply plan if web renderer does not apply css properly fix the bugs in root cause. do things in pherallel and use smalll model agents with detail guide and higher model review.`

## Task Type
bug

## Refined Goal
Make the canonical hosted and SimpleOS/QEMU window-manager paths apply the Stitch-derived macOS-like glass theme faithfully through Simple GUI and Simple Web, fixing missing wiring, unimplemented behavior, and CSS/rendering defects at their owning layers with retained semantic and framebuffer evidence.

## Acceptance Criteria
- AC-1: The selected Stitch-derived glass theme has one authoritative theme identity and produces explicit semantic values for desktop fill, window fill, title bar, border, radius, shadow, translucency/alpha, text, and active/inactive state.
- AC-2: The production hosted WM renders that theme through `SharedWmScene -> DrawIrComposition -> Engine2D`; structured Draw IR evidence and a nonblank framebuffer prove the requested computed styles reached the submitted composition without a compatibility renderer or unrelated synthetic frame.
- AC-3: The canonical SimpleOS desktop entry (`gui_entry_desktop.spl`) uses the same theme identity and canonical frame route; a fresh QEMU boot provides retained serial provenance plus an independent `pmemsave` framebuffer crop showing the themed desktop and window chrome.
- AC-4: Simple GUI widgets and WM chrome preserve the theme's background/fill, alpha, radius, border, shadow, typography, and active/inactive state instead of silently falling back to hard-coded defaults.
- AC-5: Simple Web's production HTML/WebIR-to-DrawIR path applies the CSS properties needed by the glass theme; focused semantic/layout assertions and independently rendered pixels fail on omitted or incorrectly parsed/cascaded properties.
- AC-6: Every discovered unwired or unimplemented theme path is either implemented at its canonical owner and covered by a focused regression, or remains explicitly failed/blocked with a concrete bug record; no placeholder pass, synthetic handle, private parallel renderer, fixture bypass, or raw runtime shortcut is accepted.
- AC-7: Host interaction evidence proves focus, pointer down/up, move/maximize, keyboard/text input, positive `performance.now()` delta, at least two animation frames, CSS animation application, and a post-action semantic state change with `blur_or_tolerance=false`.
- AC-8: Host and QEMU evidence record exact binary/source revision, viewport, backend and fallback state, framebuffer/readback provenance, checksum, artifact paths, and the first unavailable GPU-proof rung; screenshots alone are insufficient.
- AC-9: Relevant research, requirements, architecture, detail design, system-test plan/spec/manual, agent-task plan, operator guide, and tracking records are current and trace every AC to implementation and evidence.
- AC-10: Focused specs, host checks, QEMU checks, generated-manual quality review, direct-runtime guards, generated-spec layout guard, and final high-capability review pass once without stubs, dummy assertions, or stale evidence.

## Scope Exclusions
No new drawing IR, private widget renderer, font atlas/cache, Engine3D shortcut, platform-specific theme fork, or broad unrelated compiler/runtime repair. Compiler/runtime bugs discovered as prerequisites remain in scope only through the smallest owner-level reproducer and fix or a concrete blocking bug record.

## Cooperative Review
- Bounded sidecar lanes: (1) current-code/docs/history and theme-plan archaeology, (2) hosted WM/Simple GUI/Web renderer and CSS gap audit, (3) SimpleOS canonical entry/QEMU evidence audit. Model selection is delegated to the available agent runtime; these lanes are intentionally narrow enough for lower-capability execution.
- Merge owner: primary Codex agent in `/root`.
- Final reviewer: primary normal/highest-capability Codex agent; sidecars cannot accept done marks, exclusions, generated-manual quality, or release-blocking evidence.
- Shared interfaces: `SharedWmScene`, `DrawIrComposition`, `Engine2D`, the existing authoritative theme model discovered by research, and the existing production HTML/WebIR-to-DrawIR and `widget_tree_to_draw_ir` owners. No sidecar may invent replacement interfaces.
- Manual steps: `Load the Stitch glass theme`; `Render the hosted WM through the canonical scene`; `Apply glass CSS and widget computed styles`; `Boot the canonical SimpleOS desktop in QEMU`; `Capture and compare semantic and framebuffer evidence`.
- Setup/checker helpers: reuse or extend the canonical hosted WM/theme checker, `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`, and the canonical SimpleOS QEMU framebuffer wrapper identified by research; provisional new helpers must be named `check-wm-glass-theme-host-evidence.shs` and `check-wm-glass-theme-simpleos-qemu-evidence.shs` only if no owner exists.
- Fail-fast placeholders: any temporarily introduced checker/spec helper must call `fail("wm glass theme evidence not implemented")` or `assert(false)` until real semantic and framebuffer assertions replace it.
- Generated-manual review owner: primary Codex agent after sidecar findings are merged.

## Runtime Boundary Decision
- runtime_need: none established during goal refinement.
- facade_checked: pending research of existing UI, renderer, QEMU, file, process, and environment facades.
- chosen_path: `reuse-facade`.
- rejected_shortcuts: raw `rt_*` aliases, fixture-only theme branches, backend field pokes, compatibility WM renderers claimed as canonical, synthetic GPU/readback evidence, and hard-coded browser pixels.

## Research Summary

- Current theme authority: `config/themes/theme.sdn` selects `aetheric_dark`.
- Conflicting history: commit `2248995c72` introduced hard-coded light Aqua WM
  defaults without promoting them to the package registry.
- Hosted root causes: the production theme-to-WM adapter is unwired; Simple Web
  emits hard-coded CSS; RGBA, shadow, gradient, and backdrop-blur semantics are
  lost or incomplete before Draw IR.
- SimpleOS authority: canonical evidence must use x86_64
  `gui_entry_desktop.spl` and `engine2d_wm_frame_executor.spl`, not legacy
  `wm_entry.spl`.
- Existing QEMU framebuffer evidence is nonblank and interactive but lacks a
  resolved theme fingerprint and structured glass witnesses.
- User selected Feature A and NFR A: registered `aetheric_dark` is the single
  authority; host/SimpleOS require exact semantic parity with
  capability-declared pixel evidence.

## Phase
implementation-blocked-inferred-text-result-provenance

## Log
- dev: Created state file with 10 acceptance criteria (type: bug); defined bounded cooperative lanes, canonical interface constraints, evidence steps, and fail-fast policy.
- research: Consolidated three parallel read-only audits; wrote local/domain
  research and selectable feature/NFR options. No implementation choice was
  inferred because repository policy requires user selection.
- requirements: User selected Feature A + NFR A. Promoted the selections to
  final requirement documents and deleted all option artifacts.
- design: Three bounded read-only reviews converged on explicit package-to-
  snapshot bootstrap projection, existing canonical render owners, and
  capability-declared semantic/pixel evidence. Added architecture, GUI/TUI,
  detail design, system-test plan, agent tasks, and fail-fast executable spec.
- implementation: Added a content-addressed renderer-neutral theme snapshot,
  exact generated bare-metal snapshot, host and SimpleOS first-frame WM
  installation, package-owned Simple Web CSS/cache identity, RGBA parsing,
  multi-shadow/backdrop semantic preservation, and named solid-material raster
  fallback. Focused source checks and generator execution passed.
- verification: Canonical hosted capture stopped before rendering on the
  existing self-hosted `HostedCaptureFramebuffer.put_pixel` lowering defect;
  recorded `hosted_wm_capture_put_pixel_lowering_2026-07-19.md`. Canonical QEMU
  verification was not started because another repository lane owns a live
  QEMU process. Fail-fast system evidence remains intentionally unresolved.
- qemu-actual: Launched the canonical x86_64 `gui_entry_desktop.spl` wrapper
  in isolated `build/wm_glass_theme_qemu_actual`. Cycle 1 exposed hosted
  `theme_package` execution in bare metal and faulted before the first frame.
  Fixed the boundary by embedding composed CSS in the generated snapshot and
  using the installed snapshot before any hosted package fallback. Cycle 2
  reached production readiness and identified the expected Aetheric taskbar
  clock-oracle change. Cycle 3 PASS retained independent QMP pmemsave pixels,
  matching guest/host font-region SHA-256, nonblank 4K frames, correlated F11
  maximize/restore, 20,043,014 changed bytes, and exact restored checksum.
- visual-review: Inspection of retained PASS images found the Simple Web
  Engine2D heuristic still matched WM class names inside CSS and overpainted
  content with legacy `#2050A0/#182230`. Removed that heuristic for WM content,
  routed it through real selector/layout rendering, and mapped content fill and
  text to package variables. Source checks pass. Per the mandatory three-cycle
  cap, this post-review pixel correction must be re-captured in a fresh session;
  the retained PASS report predates only this final content-color correction.
- continuation-2026-07-24: A fresh cache proved the July 20 striped framebuffer
  predates the current renderer source. Directly routing the full Aetheric CSS
  into the bare-metal selector/layout path remains unsafe. Added explicit
  `solid-material` background/foreground metadata from the installed
  `ThemeRenderSnapshot`; Simple Engine2D now strips package selector CSS only
  for that declared fallback and renders the original body through the real
  layout/text painter. Browser engines still consume the full Stitch CSS.
- continuation-2026-07-24-tooling: Resolved concurrent rebase markers in the
  canonical wrapper and `gui_entry_desktop.spl` to the retained Aetheric
  taskbar hash `addf76...`. The deployed CLI is stale on
  `rt_process_spawn_guarded`; today's pure-Simple Stage-3 compiler
  (`6175ea...`) successfully built the patched kernel.
- continuation-2026-07-24-qemu: The old Stage-3 compiler entered SimpleOS but
  faulted in `sfnt.find_table` before a frame. Two launches of the fresh
  Stage-3 kernel then failed identically in OVMF/GRUB with #GP
  `RIP=FFF1000000000000` before `[BOOT32]`. Recorded
  `simpleos_wm_uefi_pre_kernel_gp_fresh_stage3_2026-07-24.md`; no current-source
  framebuffer exists. Stopped at the mandatory third cycle.
- continuation-2026-07-24-host: The patched x86_64 entry closure compiled
  `658` files with `0` failures using pure-Simple Stage 3. The focused hosted
  spec reached the test daemon but timed out after its one permitted run.
  Working and staged direct-env/runtime guards pass, `git diff --check` passes,
  no conflict markers remain, and `doc/06_spec` contains zero executable
  `*_spec.spl` files. Runtime host assertions and current-source QEMU pixels
  remain unproven.
- continuation-2026-07-24-review: Highest-capability review rejected the
  selector-free fallback document because it discarded canonical package CSS
  and affected hosted Engine2D. Removed that rewrite. Renderer-neutral
  fallback metadata remains on the WM root while the original full document
  flows through the canonical CSS/layout owner.
- continuation-2026-07-24-ovmf: Added the EFI GOP/video modules and text
  payload already proven by the canonical readiness wrapper. Three fresh
  launches now reach font registration, shell/app startup, compositor
  software fallback, FAT32, and a 3840x2160 ARGB scanout; the former
  pre-kernel GP is resolved.
- continuation-2026-07-24-span-blocker: All three launches stop on the first
  CSS scan. RIP is in `ByteSpan.starts_with` (previously `equals`) with return
  address in `_css_scan_rules_simple`. A direct comparison experiment moved
  but did not fix the fault and was reverted. Recorded
  `simpleos_wm_freestanding_bytespan_css_scan_fault_2026-07-24.md`; the QEMU
  cycle cap is exhausted and pixel evidence remains blocked.
- sync-2026-07-24: Fetched GitHub and confirmed `main@origin` matches local
  `main` at `058f1338` (parser parity fix). The 85-file dirty tree contains
  WM/theme, unrelated `llm_caret`, shared, and external lanes, while another
  agent owns a live full-bootstrap process; no mixed or unverified working-copy
  commit was pushed.
- sync-continuation-2026-07-24: Fetched GitHub with the `$sync` workflow;
  `main@origin` and the working parent match at `52d0c716f0d1`, and the tracked
  file-count guard remained `105960 -> 105960`. Mixed WM and unrelated
  concurrent-session changes remain uncommitted and were not pushed.
- inferred-text-provenance-2026-07-24: Built exact pure-Simple bootstrap
  compilers from the synchronized tree. QEMU cycle 2 used compiler
  `bc99e6c6...`, built a 658-file kernel with zero failures, reached the
  3840x2160 production scanout, then faulted in `ByteSpan.starts_with` from
  `_css_scan_rules_simple`. Strengthening the fixture from explicit
  `opener: text` to inferred `opener` reproduced a direct custom-owner
  relocation. Three compiler/probe iterations did not clear that relocation;
  the final RED object and exact resume command are recorded in
  `simpleos_wm_freestanding_bytespan_css_scan_fault_2026-07-24.md`. Per the
  hard cap, QEMU cycle 3 and the hosted runtime gate were not run.
- continuation-bootstrap-wiring-2026-07-24: Resumed in the isolated
  `build/worktrees/wm-glass-theme` worktree from `origin/main` at
  `3721a30541`. Read-only sidecars confirmed the host production entry bypassed
  the package snapshot installer and ARM64 never installed the generated
  Aetheric snapshot. Added one hosted owner helper and one freestanding-safe
  SimpleOS owner helper; the host now installs the resolved snapshot before
  backend/compositor construction and uses its desktop fill, while x86_64 and
  ARM64 install the same generated snapshot before compositor construction.
  A focused three-scenario source contract passes diagnostically, but the
  deployed CLI delegates to the Rust seed and is not admissible production
  evidence. Host event receipts, current-source host pixels, x86_64 QEMU
  pixels, and ARM64 framebuffer/input evidence remain active gaps.
- continuation-compiler-check-2026-07-24: The first current-source Cargo
  command used `--exact` and filtered out the intended inferred-text
  regression, so it was rejected as evidence. The corrected name-filtered run
  passed the intended test exactly once: `1 passed; 3346 filtered out`.
- continuation-history-audit-2026-07-24: Read-only history/source review found
  three first-loss owners beyond bootstrap: Simple GUI discards `app.theme`
  before fixed-palette widget Draw IR; Simple Web selects legacy generated
  glass CSS instead of package-resolved CSS; and WM chrome flattens the render
  snapshot to colors before fixed-geometry Draw IR. Runtime theme switching
  also loads tokens without installing/notifying a snapshot. Separate
  non-overlapping implementation sidecars now own the first three boundaries.
- continuation-static-gates-2026-07-24: Working/staged direct-env/runtime
  guards, `git diff --check`, and the `doc/06_spec` executable-layout guard
  pass. The available Stage-3 artifact identifies as a pure-Simple bootstrap
  compiler but has no `check` command; no product runtime claim is admitted
  from it.
- continuation-parallel-fixes-2026-07-24: Three non-overlapping sidecars
  removed the legacy Web CSS authority, passed resolved theme snapshots into
  canonical widget Draw IR, and retained renderer-neutral WM glass identity
  and effect requests in WM Draw IR. Web passed 3 scenarios and widget Draw IR
  passed 2 scenarios using the Rust bootstrap driver; both are diagnostic,
  not product admission. The focused broad window-scene spec timed out at
  120 seconds with no assertion result and is recorded in
  `window_scene_draw_ir_spec_timeout_2026-07-24.md`. No retry was made.
- continuation-input-and-switching-2026-07-24: Host production evidence now
  records distinct real winit/FIFO key-down, key-up, pointer-move,
  pointer-button-down, and pointer-button-up receipts while retaining the
  canonical compositor calls. Six focused scenarios pass diagnostically; the
  product entry check is still blocked on `rt_process_spawn_guarded`. No
  canonical title-command/body-input API exists, so none was fabricated.
  ARM64 QMP input remains blocked before rendering by missing VirtIO-MMIO
  device discovery/eventq/backend/device attachment; a two-scenario system
  contract remains fail-fast. Runtime theme switching remains blocked by a
  missing notification transport ABI; its contract was placed under system
  tests, not the unit suite.
