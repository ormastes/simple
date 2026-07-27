# Hosted Browser Renderer Entry Isolation Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 5 | 5 | 0 | 0 |

## Covered boundaries

- Dispatch the hidden renderer worker before initializing host UI services.
- Keep renderer startup READY-gated with bounded IPC and validated frames.
- Route production browser pixels, navigation, input, and animation through
  the isolated worker and external-frame gate.
- Keep trusted address/title input separate from hostile page input.
- Persist learned or removed HSTS state after broker polling and before frame
  processing, clearing dirty state only after success and retrying failures on
  a bounded one-second cadence.

Requirement trace: REQ-WEB-BROWSER-011, REQ-WEB-BROWSER-017.

Source:
`test/01_unit/os/hosted/hosted_browser_renderer_entry_source_spec.spl`

Updated: 2026-07-27.
