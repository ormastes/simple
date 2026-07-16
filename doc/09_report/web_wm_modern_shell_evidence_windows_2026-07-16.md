# Web WM Modern Shell Evidence

- status: `pass`
- reason: `pass`
- preview: `build\test-artifacts\02_integration\app\ui\web_wm_modern_shell_evidence_windows\simple_wm_modern_preview.html`
- ARGB: `build\test-artifacts\02_integration\app\ui\web_wm_modern_shell_evidence_windows\simple_wm_modern_preview_argb.json`
- PNG: `build\test-artifacts\02_integration\app\ui\web_wm_modern_shell_evidence_windows\simple_wm_modern_preview.png`
- audit: `build\test-artifacts\02_integration\app\ui\web_wm_modern_shell_evidence_windows\simple_wm_modern_preview_audit.json`
- interaction: `build\test-artifacts\02_integration\app\ui\web_wm_modern_shell_evidence_windows\simple_wm_modern_preview_interaction.json`
- interaction PNG: `build\test-artifacts\02_integration\app\ui\web_wm_modern_shell_evidence_windows\simple_wm_modern_preview_after_interaction.png`
- log: `build\test-artifacts\02_integration\app\ui\web_wm_modern_shell_evidence_windows\electron_capture.log`
- interaction log: `build\test-artifacts\02_integration\app\ui\web_wm_modern_shell_evidence_windows\electron_interaction.log`
- simple runtime: `bin\simple.cmd`
- simple runtime source: `windows-simple-cmd`
- simple runtime status: `pass`

## Out-of-tree Invocation Proof

The 2026-07-16 Windows wrapper was rerun from
`C:\Users\ormas\AppData\Local\Temp` by absolute script path:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-web-wm-modern-shell-evidence.ps1 -BuildDir build\test-artifacts\02_integration\app\ui\web_wm_modern_shell_evidence_windows
```

The rerun kept the real launch/capture path green:
`web_wm_modern_shell_evidence_status=pass`,
`web_wm_modern_shell_evidence_bitmap_nonblank_status=pass`,
`web_wm_modern_shell_evidence_audit_pass=pass`,
`web_wm_modern_shell_evidence_interaction_pass=pass`, and
`web_wm_modern_shell_evidence_interaction_event_count=13`.
