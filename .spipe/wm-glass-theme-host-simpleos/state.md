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

## Phase
dev-done

## Log
- dev: Created state file with 10 acceptance criteria (type: bug); defined bounded cooperative lanes, canonical interface constraints, evidence steps, and fail-fast policy.
