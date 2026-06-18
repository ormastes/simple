# SSpec API Capture Helpers Agent Plan

Status: done — Current API Slice complete; provider wiring remains deferred below
Owner: Codex API slice
Date: 2026-05-30
Completed: 2026-06-18

## Scope

Build the API/protocol helper layer first. Web, GUI, and TUI provider wiring are
owned by other agents and should not block this API slice.

## Current API Slice

- Restore and keep `std.common.spec.scenario_helpers` as the common helper entrypoint.
- Provide evidence-producing checker helpers for common `Then_*` text, status,
  and JSON-field assertions.
- Provide execution capture helpers for command, args, input trigger, stdout,
  stderr, exit code, and exit-code checker evidence.
- Provide binary capture helpers for format, raw-byte summaries, decoded fields,
  and field comments.
- Provide redaction-aware API/protocol field summaries.
- Provide structured `capture_api_protocol_fields(...)` for provider code that
  already has parsed request, header, and response fields.
- Record sensitive field names redacted from params, headers, and response
  fields without recording their values.
- Provide common capture-policy resolution for step, function/checker,
  scenario, file, folder, root, then built-in defaults.
- Keep helpers pure except for the existing file-exists extern used by checker
  tests.
- Verify with focused unit tests before committing.

## Completion Evidence

- Implementation: `src/lib/common/spec/scenario_helpers.spl` provides the
  checker/evidence helpers, exec/binary/UI/API/protocol capture helpers,
  redaction helpers, and `capture_api_protocol_fields(...)`.
- Capture policy: `src/lib/common/spec/scenario_evidence.spl` provides
  step, function/checker, scenario, file, folder, root, and built-in capture
  policy resolution.
- Focused tests:
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/spec/scenario_helpers_spec.spl --mode=interpreter`
  passed 53 tests on 2026-06-18.
- Capture-policy tests:
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/spec/scenario_evidence_spec.spl --mode=interpreter`
  passed 23 tests on 2026-06-18.
- Generated manuals:
  `doc/06_spec/test/01_unit/lib/common/spec/scenario_helpers_spec.md` and
  `doc/06_spec/test/01_unit/lib/common/spec/scenario_evidence_spec.md`.
- Normal review: approved marking this plan done only for the Current API
  Slice; the provider wiring listed below remains intentionally deferred.

## Deferred To Other Agents

- Web and browser-facing capture providers.
- TUI/GUI selected rectangle provider wiring.
- Wiring capture-policy resolution through all runtime/docgen provider call
  sites.
