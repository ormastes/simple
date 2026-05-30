# SSpec API Capture Helpers Agent Plan

Status: in progress
Owner: Codex API slice
Date: 2026-05-30

## Scope

Build the API/protocol helper layer first. Web, GUI, and TUI provider wiring are
owned by other agents and should not block this API slice.

## Current API Slice

- Restore and keep `std.common.spec.scenario_helpers` as the common helper entrypoint.
- Provide redaction-aware API/protocol field summaries.
- Provide structured `capture_api_protocol_fields(...)` for provider code that
  already has parsed request, header, and response fields.
- Keep helpers pure except for the existing file-exists extern used by checker
  tests.
- Verify with focused unit tests before committing.

## Deferred To Other Agents

- Web and browser-facing capture providers.
- TUI/GUI selected rectangle provider wiring.
- Runtime capture-policy resolution through step, function, scenario, file,
  folder, and root defaults.
