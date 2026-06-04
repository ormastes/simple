<!-- codex-design -->
# Shared UI Semantic Contract - System Test Plan

Date: 2026-06-03
Status: Candidate plan pending requirement selection

## Planned Specs

- `test/03_system/app/ui/feature/shared_ui_semantic_contract_spec.spl`
  validates state/query parity across Web, Native TUI, Electron, Tauri, and
  headless semantic helpers.
- `test/03_system/app/ui/feature/shared_ui_semantic_events_spec.spl` validates
  click, type, key, focus, resize, submit, drag, and named action dispatch.
- Existing `/api/test` endpoint specs remain protocol tests for Web and
  TUI-Web only.

## Required Evidence

- Semantic snapshots with protocol version, element list, UI state, capability
  records, and adapter status.
- Dispatch results with ok/error, affected element, and reason.
- Read-after-write state checks after every semantic command.
- Typed `semantic_adapter_unavailable` for surfaces not yet at the required
  maturity stage.

## Quality Gates

- Same fixture IDs and widget kind vocabulary across surfaces.
- Same focus and enabled/selected semantics across surfaces.
- Transport-specific render success is not accepted as semantic conformance.
- `find doc/06_spec -name '*_spec.spl' | wc -l` must return `0`.
