# Plan: Scenario-Based SSpec Manuals and Typed Capture

**Date:** 2026-05-30
**Status:** Implemented
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
- `slow_it`, explicit edge/error stress cases, and files under `test/05_perf/`:
  `folded` unless overridden.
- Helper-only or generated matcher specs: `skip` or `detail` depending on
  whether they explain user-visible behavior.

Implemented starter syntax:

- Scenario-level comments are parsed by `spipe-docgen`:
  `# @manual: show`, `# @manual: folded`, `# @manual: detail`,
  `# @manual: skip`, and `# @inline`.
- File-level comments are parsed by `spipe-docgen`: `# @manual-file: folded`,
  `# @manual-file: skip`, `# @manual-file: detail`, and
  `# @manual-file: show`. Scenario-level manual metadata overrides the file
  default.
- Folder/root configs are parsed by `spipe-docgen`: nearest `.sspec-manual` or
  `sspec-manual.sdn` with `manual: folded|skip|detail|show` sets the default
  for specs below that folder.
- Scenario and step capture comments are parsed by `spipe-docgen`:
  `# @capture`, `# @capture(api)`, and
  `# @capture(after_scenario, gui)`. Generated manuals render capture intent
  and remove capture metadata comments from the runnable source block.
- Previous-scenario comments are parsed by `spipe-docgen`: `# @prev("title")`
  prepends the referenced scenario body, and bare `# @prev` prepends the
  nearest previous scenario body. Expanded manuals do not print `Previous:`.
- Include comments are parsed by `spipe-docgen`: `# @include("title")`
  expands the referenced scenario body at that line and removes the include
  metadata from the rendered source block.
- Missing `# @prev` and `# @include` targets render a `Manual warnings` block
  in generated docs instead of leaking metadata into the source block.
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
- `on_failure`

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
- `gui` capture prefers HTML evidence when the GUI surface is Simple Web or
  otherwise has an HTML backing document available. Screenshot/image GUI
  evidence remains the fallback when HTML cannot be captured.
- `html` capture records both source markup and visible text summaries so
  generated manuals can check what the user sees without matching hidden
  implementation details.
- Evidence display is user-selectable with `# @evidence-display: embed_tui`,
  `# @evidence-display: links`, `# @evidence-display: embed_all`, or the
  doc-block metadata line `**Evidence Display:** ...`. The built-in default is
  `embed_tui`: embed TUI captures when possible and link screenshots, logs, and
  other artifacts.

## Checker and Capture Library

Create a shared SSpec support library rather than scattering helper functions:

- Starter implementation exists in `src/lib/common/spec/scenario_evidence.spl`:
  `ScenarioCaptureMode`, `ScenarioCaptureKind`, `ScenarioCapturePolicy`, and
  `ScenarioEvidenceArtifact` with helpers for root default capture off, bare
  after-step TUI capture, explicit enum capture policies, redacted artifacts,
  API evidence, execution evidence, binary evidence, checker-linked evidence,
  and manual evidence summaries.
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
   - Starter progress: `test/README.md` now states that generated
     `doc/06_spec/...` output must read as scenario-based manuals for
     user-visible, system, protocol, MCP, UI, hardware, and environmental
     tests.
   - Starter progress: `doc/07_guide/testing/sspec_scenario_manual.md`
     documents inline/previous/include metadata, capture kinds, environmental
     evidence, MCP manual shape, visibility policy, and implemented manual
     warning diagnostics for generated manuals.
   - Update `test/README.md`, testing guide, SPipe skills, and verification
     skills to require manual-quality generated docs.
2. **Docgen metadata parser**
   - Parse `@step`, `@capture`, `@prev`, `@inline`, `@include`, and
     `@manual(...)` as docgen metadata without changing runtime semantics.
   - Starter progress: `spipe-docgen` parses scenario-level comment metadata
     for manual visibility and inline hiding.
   - Starter progress: `spipe-docgen` parses file-level `# @manual-file`
     metadata for whole-file show/folded/detail/skip defaults.
   - Starter progress: `spipe-docgen` resolves folder/root manual visibility
     config from nearest `.sspec-manual` or `sspec-manual.sdn`.
   - Starter progress: `spipe-docgen` parses comment capture metadata for
     scenario-level and step-local capture summaries.
   - Starter progress: `spipe-docgen` expands `# @prev("title")` and bare
     `# @prev` into scenario bodies without rendering a `Previous:` label.
   - Starter progress: `spipe-docgen` expands `# @include("title")` at the
     call site.
   - Starter progress: missing `# @prev` and `# @include` targets render manual
     warnings.
   - Starter progress: invalid scenario `# @manual` and scenario/step
     `# @capture(...)` metadata now render actionable manual warnings instead
     of silently degrading to a misleading default capture or visibility.
   - Validate enum-like values and produce actionable diagnostics.
3. **Scenario graph expansion**
   - Build a scenario graph keyed by scenario title/id.
   - Starter progress: expand `# @prev` before scenario steps.
   - Starter progress: expand `# @include` at call sites.
   - Hide `@inline` scenarios from top-level manual output.
   - Starter progress: detect missing inline targets in rendered docs.
   - Starter progress: direct `# @prev` and `# @include` scenario expansion
     cycles now render manual warnings and keep the current scenario body
     usable instead of silently stripping recursive metadata.
4. **Manual renderer**
   - Starter progress: render derived manual steps first for call-like
     scenario lines, leaving assertion mechanics in the folded executable
     block.
   - Starter progress: derived manual steps skip control-flow mechanics while
     still rendering nested call-like actions.
   - Starter progress: checker-style calls such as `Then_login_succeeds()`
     render as readable manual steps.
   - Starter progress: `# @step: Text` and `# @step("Text")` label the next
     call-like manual step and are stripped from the folded executable source.
   - Starter progress: explicit `# @step` labels can also anchor to the next
     executable non-assertion setup/action line, which supports protocol specs
     where the manual action is request construction rather than a helper call.
   - Starter progress: empty `# @step` metadata renders a manual warning and
     falls back to the derived step label.
   - Starter progress: unused `# @step` metadata renders a manual warning when
     no following call-like step exists.
   - Starter progress: step-local `# @capture(...)` may appear between
     `# @step` and the labeled call-like step.
   - Starter progress: capture summaries are fallback-only when no visible
     manual step can be derived; otherwise scenario and step-local capture
     policies render under the visible step.
   - Starter progress: scenario-level `after_scenario` capture attaches only
     to the final derived manual step.
   - Starter progress: step-local `# @capture(off)` suppresses inherited
     scenario capture for that step.
   - Starter progress: `# @capture(off)` stays silent in fallback capture
     summaries.
   - Starter progress: executable SPipe source now renders inside a folded
     `Executable SPipe` details block by default when a scenario has runnable
     body content.
   - Starter progress: fixed blank executable source after expanded `# @prev`
     and `# @include` bodies by avoiding interpreter array iteration paths that
     blanked copied text during expansion and dedent.
   - Render advanced/edge/detail scenarios according to visibility policy.
5. **Typed evidence model**
   - Starter progress: added pure shared evidence/capture model in
     `src/lib/common/spec/scenario_evidence.spl` and focused unit coverage in
     `test/01_unit/lib/common/spec/scenario_evidence_spec.spl`.
   - Starter progress: added API, exec, binary, redacted, and checker-linked
     evidence constructors.
   - Replace separate evidence rendering internals with `EvidenceArtifact`.
   - Keep backward-compatible metadata fields while migrating.
6. **Capture providers**
   - Implement `tui`, `text`, `exec`, `api/protocol`, and `log` first.
   - Implement `gui` selection/highlight helpers next.
   - Implement `binary` structured decoder last.
   - Progress: `scenario_helpers` exposes provider-facing API/protocol,
     execution, binary, TUI, and GUI capture helpers. The provider helpers
     preserve scenario/step ids, redact sensitive API/protocol fields, retain
     command input/stdout/stderr/exit evidence, retain binary raw-byte and
     decoded-field summaries, and capture TUI/GUI selected rectangles,
     highlight targets, inverted active menu state, visible-state summaries,
   and artifact paths.
   - Progress: HTML-aware helpers now capture Simple Web GUI surfaces as
     `html` evidence when markup is available, expose visible-text checks, and
     model checker output from `simple_html_heuristic`, `nu_html_checker`,
     `html_validate`, `axe_core`, and `playwright_locator`.
   - Progress: generated docs now label GUI capture as HTML-preferred when
     available, embed TUI evidence, and keep screenshots/other evidence linked
     by default.
   - Progress: evidence rendering now supports user-selected `embed_tui`,
     `links`, and `embed_all` display policies from source comments or metadata.
7. **Repository uplift**
   - Improve MCP scenario manuals first as the exemplar. Use
     `doc/03_plan/sys_test/mcp_scenario_manual_quality.md` as the target shape
     and review checklist.
   - Starter progress: added scenario-manual metadata to
     `test/02_integration/app/mcp_stdio_integration_spec.spl` and rewrote
     `doc/06_spec/app/compiler/feature/mcp_stdio_integration_spec.md` as the
     first MCP manual-quality target.
   - Starter progress: added operator `# @step` labels and step-local
     protocol/API capture hints to `test/02_integration/app/mcp_stdio_integration_spec.spl`;
     temp docgen now emits operator steps ahead of the folded executable source.
   - Add feature request to upgrade all generated SSpec docs to hand-written
     manual quality.
   - Iterate: write scenario, generate doc, evaluate like a manual, update
     helper steps/captures, repeat until quality is acceptable.

## Verification Gates

- Generated doc has a manual-first scenario section.
- Auto-generated scenario docs place `## Scenarios` immediately after the
  title, before At-a-Glance, Overview, and summary tables.
- Scenario summary tables follow the scenario body instead of preceding the
  operator flow.
- Inline/previous scenarios expand without printing redundant `Previous:`.
- Executable SPipe is folded by default.
- Folded executable blocks include runnable source line-count summaries.
- Folded executable blocks state that they contain the complete executable
  scenario source for reproduction.
- Scenario captures appear under the step that caused them.
- GUI captures document the HTML-preferred fallback when a Simple Web/HTML
  backing document is available.
- HTML captures include visible text summaries for user-facing checks.
- Evidence rendering honors user selection while defaulting to embedded TUI and
  linked non-TUI artifacts.
- Step-local provider artifact metadata appears under the step that caused it.
- Step capture labels use typed wording such as `Protocol capture` and
  `API capture`.
- Protocol/API/exec captures appear under the manual step that produced them.
- Captured steps with generated expected checks include compact `Evidence:`
  previews under the step.
- Boolean assertion summaries render as expected-result bullets under the
  manual step that produced them.
- Long JSON expected values are shortened in visible summaries while the full
  assertion stays in folded executable source.
- Detailed edge/advanced scenarios are folded or skipped according to policy,
  and intensive matrix/stress/schema/OOM/loop detail scenarios fold by default.
- Environmental tests show meaningful `exec`, `protocol`, `api`, `binary`, or
  `log` evidence instead of empty screenshots.
- MCP scenario manual is reviewed as a hand-written-quality exemplar.

Current verification note: syntax checks pass. The scenario evidence unit test
passes 21/21, `test/01_unit/lib/common/spec/scenario_helpers_spec.spl` passes
44/44, and `test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl`
reports 50 examples / 0 failures after replacing unsupported negative matchers
with built-in assertions, fixing the `spipe-docgen` runtime path issues found
during the manual-generation check, adding metadata warning/cycle diagnostic
coverage, fixing blank folded executable output for expanded scenarios, adding
derived manual steps and `# @step` labels, and making detached capture summaries
fallback-only when no visible manual step can be derived. It also verifies
scenario-level `after_scenario` capture attaches only to the final derived
manual step and step-local `# @capture(off)` suppresses inherited scenario
capture, including fallback summary rendering, and multiple manual warnings
render without blanking entries. It also covers step-local capture metadata,
including `# @capture(off)`, between a `# @step` label and the labeled action,
explicit `# @step` labels on executable setup lines, and stable `# @prev`
source expansion with step-local capture metadata. It also verifies generated
expected-result bullets for boolean contains assertions, including normalized
escaped JSON string fragments, and truncates long expected-result values while
preserving the full assertion in folded executable source. The direct spec run
still exits nonzero after reporting 50 examples / 0
failures because of the existing
repo-level `compiler_driver_create` semantic finalization issue also noted in
`doc/03_plan/port_rust_c_to_pure_simple.md`.

Temp MCP stdio docgen now emits `## Scenarios` immediately after the title,
with At-a-Glance, Overview, and Scenario Summary following the operator
scenario body. The generated MCP steps include expected-result bullets from
protocol/API assertions, with escaped JSON fragments normalized for manual
reading. Step captures render as typed labels such as `Protocol capture:
after_step` and `API capture: after_step`. Captured protocol/API steps include
compact evidence previews derived from expected checks. Folded executable
blocks include runnable source line counts for reproduction review, and long
expected values are shortened with a pointer to the folded executable source.

## First Exemplar: MCP

MCP is the first manual-quality target because it exercises non-UI evidence:
protocol frames, tool calls, command execution, logs, and matrix/detail cases.
The current generated docs for `mcp_protocol_runtime` and `mcp_stdio_integration`
show useful test coverage, but not yet an operator manual. The exemplar plan is
`doc/03_plan/sys_test/mcp_scenario_manual_quality.md`.
