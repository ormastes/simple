# TODO: [2D] Run the full Vulkan test corpus on physical Linux

Date: 2026-09-27
Status: BLOCKED — no physical Linux Vulkan host has been supplied; the
macOS-side bootstrap lanes are additionally gated on
`doc/08_tracking/bug/macos_stage2_compiler_cli_build_host_gpu_link_2026-09-27.md`.
Scope: full 2D/Web/GUI Vulkan test corpus behind
`doc/09_report/verify_simple_2d_skia_renderdoc_hardening.md`
(REQ-2D-001..006, REQ-WEB-001..003, REQ-GUI-001..003, NFR-2D-001..002).

This todo is the test-execution companion to
`doc/08_tracking/todo/simple_2d_skia_renderdoc_linux_n2_2026-09-27.md`
(device qualification). Do both on the same admitted host, same device
UUIDs, same session.

## Prerequisites (all checked on arrival)

- [ ] Host admitted per the N2 todo: OS, GPU vendor/device, driver/API
      versions, device UUID, driver UUID recorded before any run.
- [ ] Pinned Skia checkout at `35d5edfa0d50984c22ff94f5438c31e0db12c6f8`
      synced on the host; `build-linux.shs` provider built with
      `SIMPLE_UPSTREAM_SKIA_ENABLE_AFFINE_V3=1`; receipt + manifest digests
      retained (do not copy macOS build outputs).
- [ ] Pure-Simple bootstrap deployed on the host from an admitted stage-2
      candidate (same lane discipline as macOS: planner receipt, full-lane
      `--deploy`, trusted build manifest + WM sffi libraries generated on
      host).
- [ ] Failing-assertion control run under the deployed compiler and
      recorded as failing, before any spec PASS is trusted.

## Test corpus (each row: run once, retain artifacts, record verdict)

- [ ] `check-linux-vulkan-render-log-compare.shs` (or its current successor)
      full pass on the physical device.
- [ ] `check-vulkan-2d-c-compare.shs` / `check-vulkan-2d-bit-diff.shs`
      exact-pixel and bit-diff rows.
- [ ] `check-vulkan-2d-qualification.shs` controlled-rectangle qualification
      runner on the selected device.
- [ ] Engine2D scenes `01-solid-boxes`, `06-rectangular-clip`,
      `02-fractional-edges` through the qualification runner; completed
      top-left RGBA8 readbacks; case02 analytic edge comparator verdict
      (see `doc/08_tracking/bug/skia_case02_edge_tolerance_exceedance_2026-09-27.md`
      for the open tolerance decision — apply the owner's ruling, never
      widen silently).
- [ ] Dual-backend comparison: Simple Vulkan backend vs optional upstream
      Skia Ganesh Vulkan provider on the same device; oracle digests
      `2f4d3fb1…39e9` (case01) and `0372ef52…ebb1` (case06) are
      platform-independent references pre-validated on the Mac MoltenVK
      lane; case02 comparator is shared.
- [ ] Fault injection: wrong-thread submit, device-loss, double-close,
      v3-rejected-on-default-build rows (mirror the 19/19 macOS probe set).
- [ ] Web: `check-vulkan-web-live-evidence.shs` and browser
      scroll/viewport/fixed-position rows (case41 family) on the Linux
      compositor path.
- [ ] GUI: `check-gui-vulkan-window.shs`, input before/after states, and
      `31-latin-shaping` once the private native glyph contract +
      independent oracle exist (macOS lane must land these first).
- [ ] RenderDoc captures for at least the three Engine2D scenes and one
      GUI frame; capture provenance (binary digests + device UUIDs)
      recorded. (No RenderDoc exists on the Mac — Linux is the first
      capture-capable target.)

## Gates after the corpus

- [ ] Requirement-traced SPipe specs pass under the deployed compiler
      (each expected-failure row proven by its control).
- [ ] Generated-manual docgen refreshed; `find doc/06_spec -name '*_spec.spl' | wc -l` prints 0.
- [ ] `doc/09_report/verify_simple_2d_skia_renderdoc_hardening.md` updated
      with the actual Linux artifacts (no Mac source check promoted to
      Linux device evidence).
- [ ] Handoff-plan owner review, then PR publication per
      `doc/03_plan/agent_tasks/simple_2d_skia_renderdoc_kimi_handoff_2026-09-27.md`.

References: `doc/03_plan/sys_test/simple_2d_skia_renderdoc_hardening.md`,
`tools/upstream-skia-ganesh-vulkan/README.md`,
`doc/09_report/macos_vulkan_2d_preflight_2026-09-27.md`.
Supply host connection details through secure configuration, not this
document.
