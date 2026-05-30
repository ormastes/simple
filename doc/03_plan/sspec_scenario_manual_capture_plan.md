# Plan: Scenario-Based SSpec Manuals and Typed Capture

**Date:** 2026-05-30
**Status:** Planned
**Owner:** SPipe / spipe-docgen
**Related research:**
- `doc/01_research/local/sspec_scenario_manual_capture.md`
- `doc/01_research/domain/sspec_scenario_manual_capture.md`

## Goal

Generated `doc/06_spec/...` documents should read like high-quality
scenario-based manuals while remaining generated from executable SPipe/SSpec
tests. This includes ordinary system tests and environmental tests against
external libraries, processes, emulators, hardware, and protocols.

## User Decisions Captured

- Do not add `@actor`; actor display defaults to `User`/`user` unless explicit
  metadata exists.
- Capture is off by default at root/global scope.
- A bare `@capture` enables capture with mode `after_step`.
- If capture kind is omitted, default kind is `tui`.
- Capture is not only screenshots. It includes UI, text, API/protocol,
  execution, binary, logs, and arbitrary artifacts.
- Prefer enum-like annotation values over strings:
  `@capture(api)`, `@capture(binary)`, `@manual(folded)`.
- `@prev` expands previous inline setup steps silently; do not print
  `Previous: ...` when expansion succeeds.
- `@inline` scenarios are hidden as standalone sections and appear only where
  expanded by `@prev` or `@include`.

## Target Authoring Shape

```simple
@inline
it "app opens":
    user.open_app()

@prev("app opens")
@capture
it "user logs in":
    user.enter_login("demo", "pass")

    @capture(api)
    user.submit_login()

    Then_login_succeeds()
```

Target generated manual:

```markdown
#### user logs in

1. User opens app
   Captured TUI

2. User enters login demo
   Captured TUI

3. User submits login
   API capture
   POST /login
   status: 200

4. Then login succeeds
   Captured TUI

<details>
<summary>Executable SPipe</summary>

...

</details>
```

## Manual Visibility Policy

Support this by root config, folder config, file annotation, scenario
annotation, and step annotation. Closest scope wins.

Modes:

- `manual(show)` — render as normal manual content.
- `manual(folded)` — render inside an expandable advanced/edge section.
- `manual(skip)` — omit from generated manual but keep executable tests.
- `manual(detail)` — render under folded implementation/test detail.

Default policy:

- Normal feature/system scenarios: `show`.
- `slow_it`, explicit edge/error stress cases, and files under `test/perf/`:
  `folded` unless overridden.
- Helper-only or generated matcher specs: `skip` or `detail` depending on
  whether they explain user-visible behavior.

Implemented starter syntax:

- Scenario-level comments are parsed by `spipe-docgen`:
  `# @manual: show`, `# @manual: folded`, `# @manual: detail`,
  `# @manual: skip`, and `# @inline`.
- `slow_it` scenarios fold by default unless preceded by `# @manual: show`.
- Future annotation syntax remains planned for richer runtime/docgen
  integration, but comments are the safe executable form today.

## Capture Policy

Precedence:

```text
inline step annotation
function/checker annotation
scenario annotation
file config/annotation
folder config
root config
built-in default
```

Mode values:

- `off`
- `after_step`
- `after_scenario`
- `on_fail`

Kind values:

- `tui`
- `gui`
- `text`
- `api`
- `protocol`
- `exec`
- `binary`
- `log`
- `artifact`

Rules:

- Built-in root default is capture `off`.
- Bare `@capture` means `after_step` + default kind `tui`.
- `@capture(api)` means `after_step` + kind `api`.
- `@capture(after_scenario, gui)` means one GUI capture at scenario end.
- Step-local `@capture(...)` applies only to the next rendered manual step.
- Captures attach to rendered manual steps, not to a detached evidence section.

## Checker and Capture Library

Create a shared SSpec support library rather than scattering helper functions:

- `ScenarioStep` records prose, source location, capture policy, and links to
  executable helper/checker functions.
- `EvidenceArtifact` records kind, title, mime/type, path or body, metadata,
  scenario id, step id, and privacy/redaction state.
- `CaptureProvider` implementations produce evidence for `tui`, `gui`, `text`,
  `api`, `protocol`, `exec`, `binary`, `log`, and `artifact`.
- `CheckerEvidence` lets `Then_*` helper/checker functions produce the same
  manual evidence and assertions from one source of truth.
- Binary capture supports optional structure decoders that render field names,
  values, offsets, and field comments when available.
- UI capture needs selection helpers similar to Playwright: find, act, selected
  rectangle, highlight/invert active menu item, capture visible state.

## Implementation Phases

1. **Documentation and skills**
   - Add local/domain research and this plan.
   - Update `test/README.md`, testing guide, SPipe skills, and verification
     skills to require manual-quality generated docs.
2. **Docgen metadata parser**
   - Parse `@step`, `@capture`, `@prev`, `@inline`, `@include`, and
     `@manual(...)` as docgen metadata without changing runtime semantics.
   - Starter progress: `spipe-docgen` parses scenario-level comment metadata
     for manual visibility and inline hiding.
   - Validate enum-like values and produce actionable diagnostics.
3. **Scenario graph expansion**
   - Build a scenario graph keyed by scenario title/id.
   - Expand `@prev` before scenario steps and `@include` at call sites.
   - Hide `@inline` scenarios from top-level manual output.
   - Detect missing inline targets and cycles.
4. **Manual renderer**
   - Render manual steps first.
   - Fold executable code by default.
   - Render advanced/edge/detail scenarios according to visibility policy.
5. **Typed evidence model**
   - Replace separate evidence rendering internals with `EvidenceArtifact`.
   - Keep backward-compatible metadata fields while migrating.
6. **Capture providers**
   - Implement `tui`, `text`, `exec`, `api/protocol`, and `log` first.
   - Implement `gui` selection/highlight helpers next.
   - Implement `binary` structured decoder last.
7. **Repository uplift**
   - Improve MCP scenario manuals first as the exemplar. Use
     `doc/03_plan/sys_test/mcp_scenario_manual_quality.md` as the target shape
     and review checklist.
   - Add feature request to upgrade all generated SSpec docs to hand-written
     manual quality.
   - Iterate: write scenario, generate doc, evaluate like a manual, update
     helper steps/captures, repeat until quality is acceptable.

## Verification Gates

- Generated doc has a manual-first scenario section.
- Inline/previous scenarios expand without printing redundant `Previous:`.
- Executable SPipe is folded by default.
- Scenario captures appear under the step that caused them.
- Detailed edge/advanced scenarios are folded or skipped according to policy.
- Environmental tests show meaningful `exec`, `protocol`, `api`, `binary`, or
  `log` evidence instead of empty screenshots.
- MCP scenario manual is reviewed as a hand-written-quality exemplar.

## First Exemplar: MCP

MCP is the first manual-quality target because it exercises non-UI evidence:
protocol frames, tool calls, command execution, logs, and matrix/detail cases.
The current generated docs for `mcp_protocol_runtime` and `mcp_stdio_integration`
show useful test coverage, but not yet an operator manual. The exemplar plan is
`doc/03_plan/sys_test/mcp_scenario_manual_quality.md`.
