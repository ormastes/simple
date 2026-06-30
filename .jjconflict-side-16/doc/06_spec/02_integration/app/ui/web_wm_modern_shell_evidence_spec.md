# web_wm_modern_shell_evidence_spec

Verifies the captured evidence gate for the modern Web WM shell.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Integration |
| Status | Active |
| Source | `test/02_integration/app/ui/web_wm_modern_shell_evidence_spec.spl` |
| Plan | `doc/03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md` |
| Evidence | `build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/evidence.env` |
| Report | `build/test-artifacts/02_integration/app/ui/web_wm_modern_shell_evidence/report.md` |

## Operator Flow

1. Run `sh scripts/check/check-web-wm-modern-shell-evidence.shs`.
2. Read `evidence.env`.
3. Accept `web_wm_modern_shell_evidence_status=pass` only when the ARGB bitmap is nonblank, the PNG artifact is written, and the DOM audit passes.
4. Accept `web_wm_modern_shell_evidence_status=environment-unavailable` only for explicit host/runtime blockers such as `electron-missing`, `display-missing`, `simple-runtime-unavailable`, or `simple-runtime-preview-failed`.
5. Treat any other status as a modernization evidence failure.

## Required Checks

- Preview HTML path is recorded.
- ARGB bitmap path is recorded.
- PNG bitmap path is recorded.
- DOM audit JSON path is recorded.
- Contrast threshold is `450`.
- Touch target threshold is `44`.
- Media preferences include `prefers-contrast=more` and `prefers-reduced-motion=reduce`.
- Pass evidence proves nonblank bitmap, zero unexpected overlaps, zero text clipping, zero contrast failures, and zero touch-target failures.

## Pass Evidence

On a host with `src/compiler_rust/target/release/simple`, Electron, and Xvfb
available, a passing run writes:

```text
web_wm_modern_shell_evidence_status=pass
web_wm_modern_shell_evidence_reason=pass
web_wm_modern_shell_evidence_bitmap_nonblank_status=pass
web_wm_modern_shell_evidence_audit_pass=pass
web_wm_modern_shell_evidence_unexpected_overlap_count=0
web_wm_modern_shell_evidence_clipped_count=0
web_wm_modern_shell_evidence_contrast_failures=0
web_wm_modern_shell_evidence_touch_failures=0
```

The capture log must also show `audit_pass=true` and an empty
`audit_failure_reasons=` line.

## Current Local Result

The wrapper was run on 2026-06-26 in this checkout and produced:

```text
web_wm_modern_shell_evidence_status=pass
web_wm_modern_shell_evidence_reason=pass
```

The wrapper selected `src/compiler_rust/target/release/simple` after recording
the missing deployed wrapper candidates in
`web_wm_modern_shell_evidence_simple_runtime_failures`.

## Failure Triage

- `simple-runtime-unavailable`: restore `bin/simple`, the platform release
  binary behind `bin/release/simple`, or use `src/compiler_rust/target/release/simple`.
- `electron-missing`: install or restore `tools/electron-shell/node_modules/electron/dist/electron`.
- `display-missing`: install Xvfb or run with a real display.
- `capture-failed`: inspect `electron_capture.log`; if it reports
  `audit_failed=unexpected-overlap`, fix the generated preview layout instead
  of weakening the audit.
- `audit-or-bitmap-failed`: inspect the ARGB JSON, PNG, and audit JSON for
  nonblank, contrast, target-size, clipping, or overlap failures.
