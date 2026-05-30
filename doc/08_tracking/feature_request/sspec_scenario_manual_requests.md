# SSpec Scenario Manual Feature Requests

Feature requests for upgrading SPipe/SSpec generated docs from test-oriented
documentation to hand-written-quality scenario manuals.

## Open Requests

### FR-SSPEC-MANUAL-0001 — Add scenario-step manual metadata

- **Filed-on:** 2026-05-30
- **Filed-by:** Codex
- **Target:** sspec-manual
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Support docgen metadata for `@step`, `@prev`,
  `@inline`, `@include`, and `@manual(...)` so executable SPipe tests can render
  as scenario manuals without adding new core keywords such as `@actor`.
- **Acceptance-criteria:**
  - [x] Comment-form `# @inline` scenarios are hidden as top-level manual
        sections.
  - [x] Comment-form `# @prev` expands scenario steps without printing
        `Previous:`.
  - [x] Comment-form `# @manual-file` sets whole-file show/folded/detail/skip
        defaults with scenario-level override.
  - [x] Comment-form `# @include` expands inline scenario steps at the call
        site.
  - [x] Folder/root manual visibility config sets defaults below file scope.
  - [x] Missing inline targets produce clear generated-doc diagnostics.
  - [ ] Scenario cycles produce clear diagnostics.
  - [ ] Executable SPipe source is folded by default.
- **Partial-progress:** `spipe-docgen` now supports scenario-level comment
  metadata for manual visibility: `# @manual: folded`, `# @manual: detail`,
  `# @manual: skip`, `# @manual: show`, and `# @inline`. It supports
  file-level `# @manual-file: folded|skip|detail|show`, and expands
  `# @prev("title")`, bare `# @prev`, and `# @include("title")` into the
  rendered scenario body. Generator path-aware rendering now resolves nearest
  `.sspec-manual` or `sspec-manual.sdn` with `manual:
  folded|skip|detail|show`. Missing `# @prev`/`# @include` targets render a
  `Manual warnings` block. Full annotation syntax and cycle diagnostics remain
  open.
- **Related-upfront:** `doc/03_plan/sspec_scenario_manual_capture_plan.md`
- **Related-design-doc:** tbd
- **Related-issue:** none

### FR-SSPEC-MANUAL-0002 — Add typed capture and evidence artifacts

- **Filed-on:** 2026-05-30
- **Filed-by:** Codex
- **Target:** sspec-manual
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Replace screenshot-only thinking with a shared
  `EvidenceArtifact` model for `tui`, `gui`, `text`, `api`, `protocol`, `exec`,
  `binary`, `log`, and `artifact` captures attached to scenario steps.
- **Acceptance-criteria:**
  - [x] Shared model represents bare `@capture` as `after_step` with default
        kind `tui`.
  - [x] Shared model represents root default capture as `off`.
  - [ ] Capture policy resolves by step, function/checker, scenario, file,
        folder, root, then built-in default.
  - [x] Generated docs render starter scenario and step capture summaries from
        comment metadata.
  - [ ] Generated docs render concrete provider artifacts under the step that
        caused them.
  - [ ] Existing `Screenshots`, `TUI Captures`, `Artifacts`, and `Logs`
        metadata remains backward-compatible during migration.
- **Partial-progress:** Added `src/lib/common/spec/scenario_evidence.spl` with
  enum-based capture modes/kinds, capture policy helpers, evidence artifact
  construction, redaction, and manual summary rendering. `spipe-docgen` now
  parses `# @capture`, `# @capture(api)`, and
  `# @capture(after_scenario, gui)` comments into generated manual summaries.
  Full config resolution and provider artifact attachment remain open.
- **Related-upfront:** `doc/03_plan/sspec_scenario_manual_capture_plan.md`
- **Related-design-doc:** tbd
- **Related-issue:** none

### FR-SSPEC-MANUAL-0003 — Add checker/capture helper library

- **Filed-on:** 2026-05-30
- **Filed-by:** Codex
- **Target:** sspec-manual
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Provide a shared checker/capture library so `Then_*`
  helper functions and capture providers can share formatting, decoding,
  redaction, and evidence attachment logic.
- **Acceptance-criteria:**
  - [x] Shared capture/evidence vocabulary exists for checker and provider
        implementations.
  - [x] Checkers have a shared assertion-plus-evidence data model.
  - [x] API helper foundation captures request method/path, response status,
        and response summary.
  - [x] Execution helper foundation captures command, exit code, and output
        summary.
  - [x] Binary helper foundation captures format and field summary.
  - [ ] API/protocol providers capture full params, headers, response fields,
        and redacted sensitive values.
  - [ ] Execution providers capture args, input trigger/output pairs,
        stdout/stderr, and exit code.
  - [ ] Binary providers capture raw bytes and optional decoded structure fields
        with field comments.
  - [ ] UI helpers support selected rectangle/highlight/inverted active menu
        capture for TUI and GUI.
- **Partial-progress:** Added the pure foundational model in
  `src/lib/common/spec/scenario_evidence.spl`. It now includes API, execution,
  binary, redacted, and checker-linked evidence constructors with unit coverage.
  Provider integrations, richer protocol fields, UI selection helpers, and
  domain-specific decoders remain open.
- **Related-upfront:** `doc/03_plan/sspec_scenario_manual_capture_plan.md`
- **Related-design-doc:** tbd
- **Related-issue:** none

### FR-SSPEC-MANUAL-0004 — Upgrade all generated SSpec docs to manual quality

- **Filed-on:** 2026-05-30
- **Filed-by:** Codex
- **Target:** sspec-manual
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:** Iteratively improve existing SPipe/SSpec tests so
  generated `doc/06_spec/...` output reads like a hand-written scenario manual,
  starting with MCP scenarios as the exemplar.
- **Acceptance-criteria:**
  - [ ] MCP generated docs use scenario-first manual structure.
  - [ ] MCP docs satisfy the target shape in
        `doc/03_plan/sys_test/mcp_scenario_manual_quality.md`.
  - [ ] Primary user/operator/admin flows are visible by default.
  - [ ] Edge, stress, matrix, and internal helper scenarios are folded or
        skipped by policy.
  - [ ] Environmental tests render meaningful non-UI evidence when appropriate.
  - [ ] A review checklist exists and is used before accepting new SPipe specs.
- **Related-upfront:** `doc/03_plan/sspec_scenario_manual_capture_plan.md`
- **Related-design-doc:** tbd
- **Related-issue:** none
