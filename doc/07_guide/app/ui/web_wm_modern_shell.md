# Web WM Modern Shell Evidence

Use this gate for the modern Simple Web WM preview after the static contract
`test/01_unit/app/ui/web_wm_modern_shell_spec.spl` passes.

## Command

```bash
BUILD_DIR=build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence \
EVIDENCE_ENV=build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/evidence.env \
REPORT_PATH=build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/report.md \
sh scripts/check/check-web-wm-modern-shell-evidence.shs
```

## Evidence Contract

The wrapper writes:

- `web_wm_modern_shell_evidence_status`
- `web_wm_modern_shell_evidence_reason`
- `web_wm_modern_shell_evidence_html`
- `web_wm_modern_shell_evidence_argb`
- `web_wm_modern_shell_evidence_png`
- `web_wm_modern_shell_evidence_audit`
- `web_wm_modern_shell_evidence_bitmap_nonblank_status`
- `web_wm_modern_shell_evidence_audit_pass`
- `web_wm_modern_shell_evidence_unexpected_overlap_count`
- `web_wm_modern_shell_evidence_clipped_count`
- `web_wm_modern_shell_evidence_contrast_failures`
- `web_wm_modern_shell_evidence_touch_failures`

`status=pass` means the Electron ARGB bitmap is nonblank, the PNG artifact is
written, and the structured DOM audit passed contrast, target-size, clipping,
unexpected-overlap, and media preference checks.

The same pass also requires real Electron interaction evidence:

- `web_wm_modern_shell_evidence_interaction`
- `web_wm_modern_shell_evidence_interaction_png`
- `web_wm_modern_shell_evidence_interaction_pass`
- `web_wm_modern_shell_evidence_interaction_focus`
- `web_wm_modern_shell_evidence_interaction_keyboard`
- `web_wm_modern_shell_evidence_interaction_input`
- `web_wm_modern_shell_evidence_interaction_pointer`
- `web_wm_modern_shell_evidence_interaction_clicks`
- `web_wm_modern_shell_evidence_interaction_event_count`

This proves Chromium hit-testing and browser event delivery for the rendered
static preview controls. It does not claim the future WebSocket-backed app
action path; that needs a separate full app interaction gate.

`status=environment-unavailable` is allowed only for explicit blockers such as
missing Electron, missing display support, or missing/broken Simple runtime.
It is not a visual pass.

The wrapper tries deployed runtime paths first, then falls back to
`src/compiler_rust/target/release/simple` when it is available. The fallback is
valid evidence for local development, but broken `bin/simple` or
`bin/release/simple` wrappers should still be tracked separately.
