# Feature: wm-theme-qemu

## Raw Request

$sp_dev check wm on host and simple os on qemu. and fix unwired and unimpled and bug. specially simple gui and simpwl wm does not apply theme properly which created from stitch in glass theme like mac fill. research current files and git history check theme apply plan if web renderer does not apply css properly fix the bugs in root cause. do things in pherallel and use smalll model agents with detail guide and higher model review.

## Task Type

bug

## Refined Goal

Make Stitch-derived WM CSS overrides produce the same effective theme identity and visible chrome across hosted Simple WM, Simple Web, and every supported SimpleOS QEMU desktop, with retained visual and input-event evidence.

## Acceptance Criteria

- AC-1: A valid hosted `SIMPLE_WM_THEME_FILE` override changes chrome pixels and the active snapshot, install wire, backend clear color, and browser/DrawIR cache material identity; invalid input remains a no-op.
- AC-2: A mounted guest `/THEME.CSS` override is applied after VFS mount and before the first compositor frame on each supported QEMU desktop target.
- AC-3: Each currently runnable QEMU target records a boot/capture artifact proving theme colors in visible desktop and window regions plus pointer and keyboard event handling; unavailable targets remain explicitly blocked with a linked resume command and prerequisite.
- AC-4: Simple Web's themed HTML and retained renderer frames use the same effective snapshot identity as WM chrome, so a material-only override cannot reuse stale content/cache artifacts.
- AC-5: Focused executable tests cover CSS parsing, snapshot propagation, hosted wire handoff, and Simple Web cache invalidation; plan/bug/QEMU evidence documents name all unverified environment rows.

## Scope Exclusions

- Native Vulkan/Metal backend performance/capture work outside the WM CSS and QEMU desktop proof is tracked by its owning renderer lanes.
- A QEMU-unavailable host does not silently pass a guest row.

## Cooperative Review

- Sidecars: host snapshot/wire audit, Simple Web cache-identity audit, and QEMU-plan/evidence audit.
- Merge owner: `/root`; final reviewer: `/root` on focused source/spec evidence and capability matrix.
- Shared interfaces: `apply_wm_css_theme_text`, `active_host_wm_theme_snapshot`, `simple_web_content_revision_with_theme`.
- Manual steps/helpers: `step("boot themed desktop")`, `step("capture theme pixels")`, `step("exercise pointer and keyboard")`; existing QEMU wrappers remain the setup/checker owners.
- No new fail-fast placeholder helpers are needed; unavailable QEMU rows must return explicit blocked evidence.
- Generated-manual review owner: QEMU-plan/evidence audit.

## Phase

dev-done

## Log

- dev: Created state file with 5 acceptance criteria (type: bug).
