# T32 MCP-CLI Improvements — CLI Parity Implementation Plan

**Date:** 2026-03-27
**Status:** Complete
**Requirement:** doc/plan/requirement/t32_mcp_cli_improvements.md
**Research:** doc/research/t32_mcp_cli_async_and_window_ux.md
**Design:** doc/design/t32_mcp_cli_improvements.md

## Objective

Bring the TRACE32 CLI implementation in `examples/10_tooling/trace32_tools/t32_cli/`
to practical parity with the T32 MCP server in
`examples/10_tooling/trace32_tools/t32_mcp/`.

The current gap is not only missing commands. Several exposed CLI commands are
still presentation-only stubs and do not execute TRACE32 actions. This plan
makes CLI a real execution surface backed by the same shared T32 logic as MCP.

## Current State

### Confirmed Gaps

- MCP exposes 36 tools in `t32_mcp/protocol.spl`.
- CLI top-level dispatch only exposes an older subset in `t32_cli/mod.spl`.
- Interactive shell exposes an even smaller subset in `t32_cli/cli_shell.spl`.
- Several CLI commands are stubs:
  - `field set`
  - `action do`
  - `screenshot`
  - `cmm`
- CLI parity metadata is stale:
  - `mcp_tool_names()` still lists the older subset only.

### Impact

- Users cannot rely on CLI for the same workflows supported by MCP.
- Help text overstates capability relative to actual execution.
- New MCP tools can land without any CLI parity enforcement.
- Testing is fragmented: parser/type tests exist, but parity and end-to-end CLI
  execution coverage are weak.

## Target End State

### Functional Goals

- Every MCP tool has a CLI mapping or an explicitly documented, tested exclusion.
- No CLI command that claims to execute TRACE32 is stubbed.
- Top-level CLI mode and interactive shell mode share the same execution layer.
- CLI outputs human-readable text while preserving structured response semantics.
- New MCP tools cannot be added without a parity decision and test update.

### Non-Goals

- Do not reimplement MCP business logic separately inside CLI.
- Do not add a second independent tool registry.
- Do not make shell mode feature-richer than non-interactive CLI mode.
- Do not rely on live hardware for the full test suite.

## Design Direction

### Principle 1: CLI Is a Thin Adapter

CLI should own:
- argument parsing
- help text
- human-readable rendering
- shell prompt and command loop behavior

CLI should not own:
- TRACE32 session semantics
- MCP/T32 tool business logic
- duplicate validation rules already implemented in T32 MCP helpers

### Principle 2: Shared Execution Layer

Introduce a shared bridge so CLI can call the same logic used by MCP handlers
without going through JSON-RPC framing.

Recommended split:
- `app.t32_cli.commands`
  - command registry
  - argv parsing
  - shell command parsing
  - shared subcommand descriptors
- `app.t32_cli.bridge`
  - thin wrappers over `app.mcp_t32.*` functionality
  - result normalization for CLI consumers
- `app.t32_cli.render`
  - table rendering
  - key/value rendering
  - error rendering
  - gui status rendering

### Principle 3: Single Source of Truth for Parity

CLI command inventory must be derived from or validated against the MCP tool
inventory defined in `examples/10_tooling/trace32_tools/t32_mcp/protocol.spl`.

## Package Plan

### Existing Packages to Update

- `examples/10_tooling/trace32_tools/t32_cli/mod.spl`
  - expand top-level dispatch
  - replace stub handlers with bridge calls
  - keep help text in sync with real command availability
- `examples/10_tooling/trace32_tools/t32_cli/cli_shell.spl`
  - route shell verbs into the same bridge layer as argv mode
  - add missing shell verbs for parity
- `examples/10_tooling/trace32_tools/t32_cli/error_codes.spl`
  - refresh command/subcommand inventories
  - remove stale MCP tool list duplication or validate it automatically
- `examples/10_tooling/trace32_tools/t32_cli/session.spl`
  - keep session/core state ownership here
  - expose helpers needed by the bridge where practical
- `examples/10_tooling/trace32_tools/t32_cli/window_model.spl`
  - keep catalog-driven metadata and view formatting
  - stop using it as a fake execution layer

### New Packages Recommended

- `examples/10_tooling/trace32_tools/t32_cli/commands.spl`
  - canonical CLI command table
  - subcommand parsing and usage text
  - shell/non-shell shared mapping
- `examples/10_tooling/trace32_tools/t32_cli/bridge.spl`
  - shared wrapper layer into T32 MCP/shared logic
  - typed CLI-facing result normalization
- `examples/10_tooling/trace32_tools/t32_cli/render.spl`
  - output formatting separated from execution

## Command Parity Matrix

### Already Present but Must Be Made Real

- `sessions list/open/use/info/close`
- `cores`
- `core select`
- `windows`
- `window open/show/describe`
- `field get/set`
- `action do/list`
- `screenshot`
- `cmm`

### Missing and Must Be Added

- `cmd run`
- `eval`
- `history`
- `resources list`
- `resource read`
- `headless setup`
- `area read`
- `cmm-commands`
- `status`
- `cmm-validate`
- `jobs list`
- `jobs get`
- `jobs cancel`
- `jobs result`
- `dialog parse`
- `dialog get`
- `dialog set`
- `dialog click`
- `error-check`

### Mapping Rule

Every MCP tool must map to:
- one CLI command, or
- one CLI subcommand, or
- one tested explicit exclusion entry with rationale

Target: zero exclusions.

## Work Breakdown

### Phase 1: Foundation Refactor

#### F1.1 Create shared CLI execution architecture

- Add `commands.spl`
- Add `bridge.spl`
- Add `render.spl`
- Move common parsing/usage logic out of `mod.spl` and `cli_shell.spl`
- Define canonical command descriptors with:
  - name
  - subcommand
  - usage
  - argument schema
  - MCP tool mapping
  - renderer selection

#### F1.2 Remove presentation-only execution paths

- Replace `field set` stub with real execution
- Replace `action do` stub with real execution
- Replace `screenshot` stub with real execution
- Replace `cmm` stub with real execution
- Apply same fix in shell mode

#### Acceptance

- No CLI handler prints fake “Command:” lines in place of execution.
- CLI and shell both delegate through shared bridge helpers.

### Phase 2: Existing Subset Hardening

#### F2.1 Normalize outputs for already-exposed commands

- sessions
- cores
- windows
- window show/open/describe
- field get/set
- action do/list

#### F2.2 Add structured rendering helpers

- simple scalar result renderer
- key/value object renderer
- table renderer
- error renderer
- `gui_status` footer renderer

#### Acceptance

- Existing commands produce stable output in both success and error cases.
- `gui_status` is shown consistently where relevant.

### Phase 3: Missing Core Command Coverage

#### F3.1 Raw execution commands

- `cmd run` -> `t32_cmd_run`
- `cmm run` -> `t32_cmm_run`
- `eval` -> `t32_eval`

#### F3.2 Observability/data commands

- `history` -> `t32_history_tail`
- `resources list` -> `t32_resources_list`
- `resource read` -> `t32_resource_read`
- `status` -> `t32_status_snapshot`
- `error-check` -> `t32_error_check`

#### F3.3 Headless and command-database commands

- `headless setup` -> `t32_setup_headless`
- `area read` -> `t32_area_read`
- `cmm-commands` -> `t32_cmm_commands`
- `cmm-validate` -> `t32_cmm_validate`

#### Acceptance

- Each new CLI command has:
  - top-level dispatch support
  - shell support when applicable
  - help text
  - unit and integration coverage

### Phase 4: Async and Dialog Parity

#### F4.1 Jobs

- `jobs list` -> `t32_job_list`
- `jobs get` -> `t32_job_get`
- `jobs cancel` -> `t32_job_cancel`
- `jobs result` -> `t32_job_result`

#### F4.2 Dialog commands

- `dialog parse` -> `t32_dialog_parse`
- `dialog get` -> `t32_dialog_get`
- `dialog set` -> `t32_dialog_set`
- `dialog click` -> `t32_dialog_click`

#### Acceptance

- Dialog and job workflows are available in both CLI entry and shell mode.
- Rendering is concise and workflow-friendly, not raw JSON dumps by default.

### Phase 5: Parity Guardrails

#### F5.1 Inventory parity enforcement

- Add parity spec comparing CLI command registry against MCP tool registry
- Fail if MCP adds a tool without CLI mapping or tested exclusion

#### F5.2 Documentation sync

- Update `doc/guide/tools/t32_cli.md`
- Update `doc/guide/tools/mcp_t32.md` only if response contracts change
- Keep command examples aligned with implemented behavior

#### Acceptance

- Parity regressions fail in CI/test runs.
- Docs no longer advertise commands that are stubbed or absent.

## SSpec Test Plan

### Unit Tests

Target directory:
- `test/unit/app/t32_cli/`

#### New specs

- `command_registry_spec.spl`
  - command descriptors exist for all CLI commands
  - usage/help text is non-empty
  - each command maps to expected MCP tool
- `arg_parser_spec.spl`
  - valid argv parsing
  - missing argument failures
  - invalid subcommand failures
  - shell command parsing parity with argv parser
- `render_spec.spl`
  - object rendering
  - table rendering
  - error rendering
  - gui status rendering
- `bridge_spec.spl`
  - wrapper calls expected shared helpers
  - error passthrough
  - result normalization
- `parity_spec.spl`
  - MCP tool list and CLI registry stay aligned

#### Existing specs to expand

- `shell_spec.spl`
  - add new verbs
  - add multi-word command parsing
  - add argument edge cases
- `error_codes_spec.spl`
  - new command/subcommand help inventories
- `session_spec.spl`
  - session/core transitions used by new commands
- `window_model_spec.spl`
  - rendering assumptions for capture/show/describe output

### Integration Tests

Target directory:
- `test/integration/app/`

#### New specs

- `t32_cli_dispatch_spec.spl`
  - top-level dispatch routes to every major command family
- `t32_cli_shell_flow_spec.spl`
  - shell loop dispatches real commands through shared bridge
- `t32_cli_mcp_parity_spec.spl`
  - compares MCP tool surface and CLI command mappings
- `t32_cli_rendering_spec.spl`
  - verifies command outputs are human-readable and stable

#### Focus

- test real package interaction, not just isolated parser functions
- avoid live TRACE32 dependency by using fake or deterministic bridge seams

### Feature-Level Specs

Target directory:
- `test/feature/app/t32_tools/`

#### Existing spec to expand

- `t32_cli_spec.spl`

Expand beyond parser/types coverage into:
- top-level command behavior expectations
- shell command behavior expectations
- parity statements for command families
- examples of user-visible workflows

### System Tests

Target directory:
- `test/system/`

#### New specs

- `t32_cli_system_spec.spl`
  - end-to-end CLI command families without live hardware dependency
- `t32_cli_headless_safe_spec.spl`
  - headless setup, area read, status, cmm validate flow
- `t32_cli_dialog_workflow_spec.spl`
  - parse/get/set/click dialog workflow using deterministic fixtures
- `t32_cli_jobs_workflow_spec.spl`
  - list/get/cancel/result flow over synthetic job state

#### System test principle

Mirror the style of `test/system/t32_mcp_lifecycle_spec.spl`:
- focus on pure helpers and end-to-end orchestration
- avoid requiring an active TRACE32 instance for baseline coverage

## Package Coverage Expectations

Coverage target means decision/branch-oriented practical coverage, not line
count vanity.

### CLI Packages

- `app.t32_cli.mod`
  - target: 95%+
  - must cover all top-level command dispatch branches
- `app.t32_cli.cli_shell`
  - target: 90%+
  - must cover shell verb parsing and prompt-state-sensitive flows
- `app.t32_cli.error_codes`
  - target: 95%+
  - all user-facing command/subcommand guidance paths covered
- `app.t32_cli.session`
  - target: 90%+
  - session selection and no-session errors covered
- `app.t32_cli.window_model`
  - target: 85%+
  - catalog-driven rendering/capture behavior covered
- `app.t32_cli.commands`
  - target: 95%+
  - command table and parser logic must be nearly exhaustive
- `app.t32_cli.bridge`
  - target: 90%+
  - success/error normalization and shared helper dispatch covered
- `app.t32_cli.render`
  - target: 90%+
  - all renderer branches and empty/error cases covered

### Parity Coverage

- 100% of MCP tools must have:
  - CLI mapping, or
  - explicit tested exclusion

Target state: 100% mapped, 0 exclusions.

## Detailed Acceptance Criteria

### Command Execution

- CLI no longer contains fake execution stubs for TRACE32-affecting commands.
- Shell mode and non-shell mode call the same backend helpers.
- Error paths are structured and consistent across command families.

### Parity

- MCP tool inventory and CLI mapping inventory are checked in tests.
- Adding a new MCP tool without CLI parity causes test failure.

### Usability

- `simple t32 help` documents all implemented command families.
- shell `help` documents all implemented shell verbs.
- outputs are readable without needing raw JSON parsing.

### Testing

- unit, integration, feature, and system test layers all exist for CLI parity
- no reliance on live hardware for the default parity suite
- optional live-hardware tests remain separate from default suite

## Implementation Order

### Wave 1

- create `commands.spl`, `bridge.spl`, `render.spl`
- replace existing stubs with bridge-backed execution
- update top-level and shell help

### Wave 2

- add raw execution, status, history, resource, headless, and validator commands
- add rendering and shared parser coverage

### Wave 3

- add jobs and dialog workflows
- add parity guard specs

### Wave 4

- update docs
- tighten coverage threshold expectations
- clean up duplication left in `error_codes.spl`, `mod.spl`, and `cli_shell.spl`

## Risks

- If CLI directly calls MCP handlers that assume JSON-RPC framing, wrapper seams
  may need extraction before parity work can proceed cleanly.
- If rendering is mixed into business logic, package split may need a small
  refactor before large command expansion.
- If shell and argv parsing diverge further during implementation, parity bugs
  will reappear unless both are forced through a shared command table.

## Exit Criteria

This plan is complete when:
- the CLI command surface matches MCP coverage
- no fake execution stubs remain
- parity is enforced by SSpec
- package-level coverage targets are met or explicitly justified
- docs reflect the implemented command surface accurately
