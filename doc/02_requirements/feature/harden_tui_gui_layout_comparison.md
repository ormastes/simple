<!-- codex-requirements -->
# Feature Requirements: Harden TUI/GUI Layout Comparison

Selected option: Feature Option 3, Full Backend Evidence Matrix.

## Requirements

REQ-001: The comparison pipeline must reject invalid viewports, truncated pixel buffers, and capture viewport metadata mismatches before exact or perceptual acceptance.

REQ-002: Exact match semantics must mean full-viewport byte-for-byte equality. Threshold or perceptual scores may be reported as diagnostics but must not imply exact acceptance.

REQ-003: Capture failures must be preserved as first-class diagnostics for both source A and source B. A failed capture must not be collapsed into a pixel mismatch or empty-buffer success.

REQ-004: Diff diagnostics for valid viewports must cover the full requested viewport and visibly mark missing or unequal pixels.

REQ-005: HTML fixture comparison and famous-site corpus comparison must use the same fail-closed pair contract: successful capture, matching viewport metadata, complete pixel buffers, exact acceptance, and diagnostic-only perceptual metrics.

REQ-006: TUI/GUI layout comparison must define a structural layer that can represent TUI cell grids, GUI/browser layout boxes, text lines, stable node labels, geometry mismatches, pixel comparison links, and backend evidence links.

REQ-007: Backend acceleration evidence must include explicit lanes for Metal, Vulkan, CUDA, and CPU SIMD. Each lane must report initialized, unavailable, failed, or fallback state without silently substituting scalar/software evidence for accelerated evidence.

REQ-008: Backend evidence reports must expose runtime API, feature gate, shader/kernel format, capability flags, device/driver diagnostics where available, and selected-backend status.

REQ-009: The implementation must preserve existing TUI/GUI behavior while hardening comparison and reporting semantics.

REQ-010: Changed executable SPipe specs must use real assertions and generated/manual scenario manuals must stay under `doc/06_spec` as `.md`, never executable `.spl`.

## Acceptance Mapping

- REQ-001 to REQ-005 are currently covered by focused comparison specs and source changes.
- REQ-006 is implemented by `src/app/wm_compare/structural_layout_report.spl`, covered by `test/system/wm_compare/structural_layout_report_spec.spl`, and wired into famous-site corpus layout-report mismatch evidence. The spec covers line structure, TUI cell geometry, GUI/browser layout boxes with stable labels, geometry mismatch diagnostics, pixel links, and backend evidence links.
- REQ-007 and REQ-008 are implemented by backend probe evidence summaries, strict backend probe specs, backend measurement records, and the current-host backend measurement matrix report. Metal, Vulkan, and CUDA are explicitly unavailable on this host; CPU SIMD has initialized measurement evidence.
- REQ-009 and REQ-010 are verified by focused regression and layout gates.
