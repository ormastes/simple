<!-- codex-research -->
# Local Research: SSpec Scenario Manual Capture

**Date:** 2026-05-30
**Scope:** Improve executable SPipe/SSpec tests so generated `doc/06_spec/`
reads like hand-written scenario manuals, including environmental tests and
typed capture evidence.

## Current State

- `test/README.md` defines the canonical executable test roots and says
  generated SPipe docs mirror `test/...` paths under `doc/06_spec/...`.
- `src/app/spipe_docgen/spipe_docgen/parser.spl` already extracts `it` bodies,
  renders runnable Simple code fences, strips leading scenario docstrings, and
  renders some custom blocks such as `m{...}`.
- `src/app/spipe_docgen/spipe_docgen/generator.spl` already supports top-level
  evidence metadata: `Artifacts`, `Screenshots`, `TUI Captures`, and `Logs`.
  It embeds image evidence and text TUI captures, but evidence is not yet
  attached to specific scenario steps.
- `src/app/feature_doc/app_docgen.spl` has a separate app manual-like generator
  that maps `describe/context/it` into behavior bullets. It is simpler than
  `spipe-docgen` and does not own the canonical `doc/06_spec/` path.
- `.codex/skills/design`, `.codex/skills/system_test`, `.codex/skills/impl`,
  `.codex/skills/verify`, and `.claude/agents/spipe/*` require SPipe tests,
  mirrored generated docs, and visible-state evidence for UI-facing specs, but
  they do not yet require manual-quality scenario output.

## Existing Capture Surfaces

- UI/TUI/GUI evidence:
  - `spipe-docgen` metadata embeds screenshots and TUI text captures.
  - Rendering tests use screenshot capture helpers under `test/integration/rendering/`.
  - `src/app/mcp/main_lazy_play_tools.spl` exposes Playwright-compatible UI
    automation paths that can eventually provide selection-aware captures.
- Text/execution evidence:
  - Test runner code captures stdout/stderr through temp files.
  - QEMU/semihosting specs capture serial and process output.
- Protocol/API evidence:
  - MCP protocol tests and HTTP server tests exist, but generated docs do not
    yet have step-local request/response capture objects.
- Binary/structured evidence:
  - Binary formats such as SMF and storage structures are documented and tested,
    but there is no shared "decode binary evidence with field comments" capture
    library for manuals.
- Hardware/environmental evidence:
  - FreeBSD QEMU, TRACE32, GDB/DAP, QEMU framebuffer, and hardware-gated tests
    exist. They are system/environmental tests that need the same manual
    scenario language, but often with command/API/log/binary evidence instead
    of GUI screenshots.

## Gaps

1. Generated docs still foreground test code and top-level evidence; they do
   not primarily render "step sentence + capture/evidence".
2. There is no `@step` prose contract for helper methods/checkers.
3. There is no `@prev`, `@inline`, or `@include` convention for reusable setup
   flows that expand silently into a scenario manual.
4. There is no scope-based manual visibility model for very detailed tests:
   file/folder/scenario/step can not yet hide, fold, or classify advanced/edge
   manual content.
5. Capture is not a typed evidence model. UI, API, text, execution, binary, log,
   and protocol captures need one shared representation.
6. Checker/helper logic and capture logic are not integrated, even though manual
   assertion evidence often needs the same formatting and decoding logic.
7. The skills do not require a "generated manual quality check and update loop"
   before accepting SPipe specs.

## Local Design Direction

- Keep executable SPipe as the source of truth.
- Add docgen/manual conventions first; avoid new core grammar unless an existing
  annotation parse path cannot express the needed metadata.
- Treat capture as typed evidence attached to scenario steps:
  `tui`, `gui`, `text`, `api`, `protocol`, `exec`, `binary`, `log`, and
  `artifact`.
- Keep default capture off. A bare `@capture` enables default `after_step`
  capture with default kind `tui`.
- Render `@inline` scenarios only when included by `@prev` or `@include`.
- Fold advanced/edge/noisy scenarios by default instead of deleting them from
  docs; allow folder/file/scenario/step policy to hide when appropriate.
