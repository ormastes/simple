# Simple CLI and simple-mcp Completeness — Requirements

**Date:** 2026-03-27
**Status:** Draft
**Plan:** doc/plan/simple_cli_mcp_completeness_plan_2026-03-27.md

## Motivation

The repository has two overlapping user-facing surfaces:

- the primary `simple` CLI in `src/app/cli/main.spl`
- the `simple-mcp` server in `src/app/mcp/main.spl`

Both are broadly functional, but completeness is inconsistent:

- some CLI commands are still placeholders or thin launchers
- some MCP tools are wrappers around CLI commands rather than first-class services
- parity between CLI, MCP, test coverage, help text, and docs is not enforced
- some capabilities are discoverable only through MCP or only through CLI

This effort defines what “complete” means for both surfaces and establishes the
required implementation and verification work.

## Scope

### In Scope

#### F1: CLI command completeness

- REQ-F1-001: Every documented top-level CLI command must be implemented or explicitly marked experimental in help/docs.
- REQ-F1-002: Placeholder commands must be either implemented or removed from user-facing help.
- REQ-F1-003: CLI subcommand parsing, help text, and dispatch must be centralized enough to avoid drift.
- REQ-F1-004: CLI commands that wrap internal apps must propagate stable exit codes and readable errors.

#### F2: simple-mcp tool completeness

- REQ-F2-001: Every tool listed by `simple-mcp` must have a real handler with validated inputs and structured output.
- REQ-F2-002: MCP tool schemas, dispatch, annotations, and result shape must stay aligned.
- REQ-F2-003: Wrapper-based MCP tools are allowed, but must be explicitly categorized and tested as wrappers.
- REQ-F2-004: Long-running MCP tools must define timeout/cancellation/task behavior clearly.

#### F3: CLI/MCP capability alignment

- REQ-F3-001: Every major project workflow must be reachable from at least one stable user surface.
- REQ-F3-002: Where CLI and MCP represent the same workflow, semantics and error behavior must be intentionally aligned.
- REQ-F3-003: Tool/command inventory drift must be detected by automated tests.
- REQ-F3-004: `simple mcp` must remain a stable server launcher, but MCP-only tools must be documented as MCP-only rather than silently assumed to have CLI peers.

#### F4: Documentation completeness

- REQ-F4-001: CLI help, `doc/guide/cli.md`, and tool guides must match actual implementation state.
- REQ-F4-002: `simple-mcp` docs must identify native tools, wrapper tools, and MCP-only tools.
- REQ-F4-003: Incomplete or intentionally deferred commands/tools must be tracked explicitly in a limitations section.

#### F5: Test and coverage completeness

- REQ-F5-001: CLI dispatch must have near-exhaustive unit and integration coverage.
- REQ-F5-002: MCP tool families must each have unit coverage and at least one integration/system path.
- REQ-F5-003: Protocol-level tests must cover initialize, tools/list, tools/call, resources, prompts, roots, logging, and shutdown behavior.
- REQ-F5-004: Coverage thresholds must be defined by package/tool family, not just globally.

## Out of Scope

- TRACE32-specific CLI parity work beyond what is already split into its own plan
- OpenAI/remote-provider product policy changes
- Introducing HTTP transport for MCP
- Replacing all shell-wrapper implementations immediately with native implementations in one step

## Functional Requirements

### CLI Surface

- REQ-CLI-001: `simple --help` must not advertise commands that call `cli_not_implemented(...)`.
- REQ-CLI-002: Command dispatch in `src/app/cli/main.spl` must have a tested ownership list for every top-level command.
- REQ-CLI-003: Commands delegated via `cli_run_file(...)` must have existence and smoke coverage.
- REQ-CLI-004: Commands delegated via shell/process wrappers must capture stdout, stderr, and exit code consistently.
- REQ-CLI-005: Package-management, build, test, lint, fix, query, MCP/LSP launch, and doc/stats workflows must each have end-to-end command coverage.

### MCP Surface

- REQ-MCP-001: `tools/list` inventory in `src/app/mcp/main_lazy_protocol.spl` must match dispatch coverage in `src/app/mcp/main.spl`.
- REQ-MCP-002: Each MCP tool family must declare whether it is:
  - native/in-process
  - wrapper-based
  - experimental
- REQ-MCP-003: Wrapper-based tools must define timeout policy and output normalization.
- REQ-MCP-004: MCP task tools must expose stable state transitions and cancellation semantics.
- REQ-MCP-005: Debug, query, diagnostics, VCS, CLI-wrapper, and test-daemon tool families must each have family-level acceptance tests.

### Alignment

- REQ-ALIGN-001: For overlapping workflows, document the canonical user-facing entry:
  - CLI-first
  - MCP-first
  - both
- REQ-ALIGN-002: Where CLI and MCP differ intentionally, document the difference and test it.
- REQ-ALIGN-003: No undocumented divergence between help text, docs, and actual behavior.

## Acceptance Criteria

### CLI

- AC-CLI-01: No command shown in help is a known placeholder.
- AC-CLI-02: Every top-level command has at least one dispatch test.
- AC-CLI-03: Every implemented command family has at least one integration or system test.
- AC-CLI-04: Unimplemented commands are either implemented or removed from help/docs.

### MCP

- AC-MCP-01: Every listed tool routes to a real handler.
- AC-MCP-02: Handler input schema and dispatch behavior are aligned for all tools.
- AC-MCP-03: Tool families have explicit maturity labels and tests.
- AC-MCP-04: Protocol handshake and core operations pass integration tests.

### Alignment and Docs

- AC-ALIGN-01: CLI and MCP inventory reports are generated or test-checked.
- AC-ALIGN-02: Docs identify MCP-only and CLI-only surfaces explicitly.
- AC-ALIGN-03: Known wrapper tools and experimental gaps are documented, not hidden.

### Testing

- AC-TEST-01: Unit, integration, and system tests exist for all major command/tool families.
- AC-TEST-02: Package coverage thresholds are defined and enforced for key CLI/MCP modules.
- AC-TEST-03: Regressions in command/tool inventory fail tests.

## Current Known Gaps

### CLI

- `migrate`, `diff`, `constr`, and `verify` still route through `cli_not_implemented(...)` in `src/app/io/cli_commands.spl`.
- command inventory is spread across `src/app/cli/main.spl`, `src/app/cli/cli_helpers.spl`, and multiple delegated entrypoints.

### MCP

- tool families are broad and mostly implemented, but not uniformly categorized as native vs wrapper.
- some tool families depend on shelling out to the `simple` binary and need explicit maturity labeling and timeout guarantees.

### Alignment

- there is no single parity/completeness report spanning CLI commands and MCP tools.
- docs do not consistently distinguish:
  - command launcher
  - fully implemented local command
  - MCP-only feature

## Verification Expectations

- Inventory checks must be automated.
- New commands/tools cannot land without tests and docs ownership.
- Coverage should be tracked separately for:
  - `app.cli.*`
  - `app.io.cli_*`
  - `app.mcp.*`

