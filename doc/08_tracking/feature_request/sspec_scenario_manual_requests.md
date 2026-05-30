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
  - [ ] `@inline` scenarios are hidden as top-level manual sections.
  - [ ] `@prev` expands inline scenario steps without printing `Previous:`.
  - [ ] `@include` expands inline scenario steps at the call site.
  - [ ] Scenario cycles and missing inline targets produce clear diagnostics.
  - [ ] Executable SPipe source is folded by default.
- **Partial-progress:** `spipe-docgen` now supports scenario-level comment
  metadata for manual visibility: `# @manual: folded`, `# @manual: detail`,
  `# @manual: skip`, `# @manual: show`, and `# @inline`. Full annotation
  syntax and scenario expansion remain open.
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
  - [ ] Bare `@capture` means `after_step` with default kind `tui`.
  - [ ] Root default capture is `off`.
  - [ ] Capture policy resolves by step, function/checker, scenario, file,
        folder, root, then built-in default.
  - [ ] Generated docs render capture evidence under the step that caused it.
  - [ ] Existing `Screenshots`, `TUI Captures`, `Artifacts`, and `Logs`
        metadata remains backward-compatible during migration.
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
  - [ ] Checkers can emit both assertions and manual evidence.
  - [ ] API/protocol helpers capture request params, response status, response
        body/fields, and redacted sensitive values.
  - [ ] Execution helpers capture command, args, input trigger/output pairs,
        stdout/stderr, and exit code.
  - [ ] Binary helpers capture raw bytes and optional decoded structure fields
        with field comments.
  - [ ] UI helpers support selected rectangle/highlight/inverted active menu
        capture for TUI and GUI.
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
