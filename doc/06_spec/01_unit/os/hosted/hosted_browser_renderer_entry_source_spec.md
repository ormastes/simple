# Hosted Browser Renderer Entry Isolation Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 7 | 7 | 0 | 0 |

## Covered boundaries

- Dispatch the hidden renderer worker before initializing host UI services.
- Keep renderer startup READY-gated with bounded IPC and validated frames.
- Route production browser pixels, navigation, input, and animation through
  the isolated worker and external-frame gate.
- Keep trusted address/title input separate from hostile page input.
- Route secondary browser toolbar, address-key, and address-text events through
  the target window's hosted session while retaining the primary isolated
  renderer owner.
- Persist learned or removed HSTS state after broker polling and before frame
  processing, clearing dirty state only after success and retrying failures on
  a bounded one-second cadence.
- Preflight HSTS/profile persistence for titlebar, keyboard, and evidence
  closes; reject a close when persistence fails, otherwise reconcile renderer,
  raster, profile, and external-frame ownership through the shared cleanup.
- Retain native renderer handles when process cleanup fails, propagate closed
  renderer/raster ownership on success, and report failed cleanup at shutdown.

Requirement trace: REQ-WEB-BROWSER-008, REQ-WEB-BROWSER-009,
REQ-WEB-BROWSER-011, REQ-WEB-BROWSER-017, REQ-WEB-BROWSER-018.

Source:
`test/01_unit/os/hosted/hosted_browser_renderer_entry_source_spec.spl`

Updated: 2026-07-27.
