# Simple CLI and simple-mcp Completeness — Implementation Plan

**Date:** 2026-03-27
**Status:** Draft
**Requirement:** doc/02_requirements/feature/simple_cli_mcp_completeness.md

## Objective

Make the primary `simple` CLI and the `simple-mcp` server complete enough to be
credible as first-class supported interfaces.

“Complete” here does not mean every implementation must be rewritten to be
purely native immediately. It means:

- no misleading help text
- no hidden placeholder commands
- no unowned tool inventory drift
- clear classification of native vs wrapper-based implementations
- strong tests at dispatch, family, and protocol levels
- documented intentional differences between CLI and MCP

## Current State Summary

### CLI

The top-level CLI in `src/app/cli/main.spl` has a broad dispatch surface with
many routed commands, but completeness is mixed:

- some commands are fully wired
- some commands delegate to app entrypoints via `cli_run_file(...)`
- some commands are shell wrappers
- some commands remain placeholders in `src/app/io/cli_commands.spl`

Examples of known placeholders:
- `verify`
- `migrate`
- `diff`
- `constr`

### simple-mcp

`src/app/mcp/main.spl` exposes a large tool surface, currently described as
`68 tools`, with families including:

- diagnostics and editing
- VCS
- debug and debug log
- CLI-wrapper tools
- analysis/query tools
- task tools
- test-daemon tools

The server is substantially implemented, but completeness needs to be hardened:

- inventory alignment
- family-level maturity classification
- wrapper-vs-native visibility
- protocol/system test depth

## Strategic Principles

### Principle 1: Stop Lying to the User

If a command or tool is visible, it must either work or be clearly marked
experimental/deferred.

### Principle 2: Inventory Is a Product Surface

Command lists and tool lists are APIs. Inventory drift is a bug and must be
tested.

### Principle 3: Wrapper Implementations Are Acceptable, But Must Be Explicit

Not every MCP tool needs to become native in one pass. But wrapper tools must:

- declare timeout behavior
- normalize output
- surface exit status
- be tested as wrappers

### Principle 4: CLI and MCP Should Share Semantics Where They Overlap

The same underlying workflow should not have contradictory behavior across
surfaces unless that difference is intentional and documented.

## Workstreams

### W1: CLI Inventory Audit and Normalization

#### Goals

- build a canonical inventory of top-level CLI commands
- classify each as:
  - implemented
  - delegated
  - wrapper-based
  - placeholder
  - experimental

#### Tasks

- extract all `case "..."` command arms from `src/app/cli/main.spl`
- map each command to:
  - local handler
  - delegated app entrypoint
  - shell wrapper
  - placeholder
- audit `print_cli_help()` in `src/app/cli/cli_helpers.spl`
- remove or mark commands whose behavior is still placeholder-only

#### Deliverables

- canonical command inventory table
- help text aligned with real state
- placeholder backlog list reduced to zero visible commands

### W2: CLI Placeholder Elimination

#### Goals

Eliminate `cli_not_implemented(...)` from user-visible command paths.

#### Target commands

- `verify`
- `migrate`
- `diff`
- `constr`

#### Resolution options per command

- implement now
- hide from default help and docs, mark experimental
- re-route to a real underlying app/module if already present
- delete dead command surface if obsolete

#### Acceptance

- no user-visible command in default help lands in a placeholder path

### W3: CLI Dispatch and Delegation Hardening

#### Goals

- make dispatch ownership explicit
- verify delegated app entrypoints exist and can be invoked
- stabilize exit-code and stderr handling

#### Focus files

- `src/app/cli/main.spl`
- `src/app/io/cli_commands.spl`
- `src/app/cli/cli_helpers.spl`

#### Tasks

- create or derive a dispatch registry view for tests
- standardize `cli_run_file(...)` usage patterns
- standardize shell-wrapper behavior:
  - stdout passthrough
  - stderr passthrough
  - exit code propagation
- document which commands are direct vs delegated vs wrapped

### W4: simple-mcp Tool Family Audit

#### Goals

Classify every MCP tool in `src/app/mcp/main_lazy_protocol.spl`.

#### Family buckets

- debug tools
- debug log tools
- diagnostics/edit tools
- VCS tools
- CLI-wrapper tools
- query tools
- task tools
- test-daemon tools

#### Per-tool classification

For each tool, record:

- handler file
- native or wrapper-based
- mutating or read-only
- timeout policy
- cancellation/task behavior if applicable
- existing tests
- missing tests

#### Deliverables

- MCP completeness inventory
- family maturity matrix

### W5: MCP Dispatch/Schema/Protocol Alignment

#### Goals

- ensure every listed tool has a dispatch path
- ensure schemas and behavior stay aligned
- tighten protocol-level guarantees

#### Tasks

- compare `make_tool_schema(...)` inventory to `dispatch_tool(...)`
- create tests that fail on missing dispatch for listed tools
- add family-level schema smoke tests
- add protocol tests for:
  - initialize
  - initialized notification
  - tools/list
  - tools/call
  - resources/list
  - resources/read
  - prompts/list
  - prompts/get
  - roots/list
  - logging/setLevel
  - ping
  - shutdown

### W6: CLI/MCP Alignment Matrix

#### Goals

Create a repo-owned mapping of workflows across surfaces.

#### Categories

- CLI-first workflows
  - build
  - test
  - lint
  - fmt
  - fix
- MCP-first workflows
  - structured multi-edit
  - prompt/resource surfaces
  - programmatic debug orchestration
- dual-surface workflows
  - status/check/read/run/query/VCS operations

#### Deliverables

- CLI vs MCP capability table
- explicit MCP-only features
- explicit CLI-only features
- documented intentional divergence

### W7: Documentation Completion

#### Targets

- `doc/07_guide/cli.md`
- `doc/07_guide/tooling/mcp.md`
- `doc/07_guide/tools/README.md`
- any tool-family guides that advertise unsupported behavior

#### Tasks

- align help/docs with actual commands and tools
- add maturity notes:
  - native
  - wrapper-based
  - experimental
- add limitations section for intentional gaps
- link the completeness plan/requirement docs

### W8: Testing and Coverage Enforcement

#### Goals

Make completeness measurable and regression-resistant.

#### Test layers

- unit
- integration
- system
- protocol/wire-level
- performance smoke where relevant

## SSpec Test Plan

### CLI Unit Tests

Target directories:
- `test/unit/app/`
- `test/unit/app/cli/`

#### New specs

- `test/unit/app/cli_command_inventory_spec.spl`
  - every top-level command accounted for
  - placeholder commands detected
- `test/unit/app/cli_help_alignment_spec.spl`
  - help text matches command inventory
- `test/unit/app/cli_wrapper_behavior_spec.spl`
  - wrapper commands propagate output and exit code consistently
- `test/unit/app/cli_command_classification_spec.spl`
  - command classification table remains current

#### Existing specs to expand

- [cli_dispatch_unit_spec.spl](/home/ormastes/dev/pub/simple/test/unit/app/cli_dispatch_unit_spec.spl)
- query specs under `test/unit/app/cli/`

### CLI Integration Tests

Target directory:
- `test/integration/app/`

#### New specs

- `cli_help_surface_spec.spl`
  - visible help commands are invokable or intentionally marked
- `cli_delegation_smoke_spec.spl`
  - delegated entrypoint commands smoke-test invocation
- `cli_placeholder_regression_spec.spl`
  - fails if visible commands still route to placeholder handlers

#### Existing specs to expand

- [cli_dispatch_spec.spl](/home/ormastes/dev/pub/simple/test/integration/app/cli_dispatch_spec.spl)
- [app_cli_intensive_spec.spl](/home/ormastes/dev/pub/simple/test/integration/app/app_cli_intensive_spec.spl)

### MCP Unit Tests

Target directory:
- `test/unit/app/mcp_unit/`

#### New specs

- `mcp_inventory_alignment_spec.spl`
  - every listed tool has dispatch coverage
- `mcp_tool_family_classification_spec.spl`
  - every tool has a family and maturity class
- `mcp_wrapper_tools_contract_spec.spl`
  - wrapper tools expose timeout/exit behavior consistently
- `mcp_protocol_surface_spec.spl`
  - tools/resources/prompts/roots/logging methods are all represented

#### Existing specs to expand

- `mcp_tools_spec.spl`
- `mcp_cli_tools_spec.spl`
- `mcp_query_tools_spec.spl`
- `mcp_debug_tools_spec.spl`
- `mcp_tasks_spec.spl`
- `mcp_protocol_spec.spl`
- `server_routing_spec.spl`

### MCP Integration Tests

Target directory:
- `test/integration/app/`

#### Existing specs to expand

- [mcp_stdio_integration_spec.spl](/home/ormastes/dev/pub/simple/test/integration/app/mcp_stdio_integration_spec.spl)
- [mcp_debug_log_tree_stdio_spec.spl](/home/ormastes/dev/pub/simple/test/integration/app/mcp_debug_log_tree_stdio_spec.spl)

#### New specs

- `mcp_protocol_full_handshake_spec.spl`
- `mcp_tools_inventory_runtime_spec.spl`
- `mcp_resources_prompts_runtime_spec.spl`
- `mcp_wrapper_tools_runtime_spec.spl`

### System Tests

#### CLI

- `test/system/cli_surface_system_spec.spl`
  - end-to-end command-family smoke matrix
- `test/system/cli_docs_help_consistency_spec.spl`
  - docs/help/inventory consistency

#### MCP

- `test/system/mcp_surface_system_spec.spl`
  - end-to-end protocol surface validation
- `test/system/mcp_family_matrix_spec.spl`
  - one representative call per major tool family

## Coverage Expectations

Coverage targets are package-oriented and should be enforced pragmatically.

### CLI Packages

- `src/app/cli/main.spl`
  - target: 95%+ dispatch branch coverage
- `src/app/io/cli_commands.spl`
  - target: 90%+ branch coverage
- `src/app/cli/cli_helpers.spl`
  - target: 90%+ help/inventory coverage
- `src/app/cli/query*.spl`
  - maintain or improve current unit/integration coverage

### MCP Packages

- `src/app/mcp/main.spl`
  - target: 95%+ dispatch branch coverage
- `src/app/mcp/main_lazy_protocol.spl`
  - target: 95%+ protocol/schema branch coverage
- `src/app/mcp/main_lazy_diag_tools.spl`
  - target: 90%+
- `src/app/mcp/main_lazy_vcs_tools.spl`
  - target: 90%+
- `src/app/mcp/main_lazy_cli_tools.spl`
  - target: 90%+
- `src/app/mcp/main_lazy_query_tools.spl`
  - target: 90%+
- `src/app/mcp/main_lazy_debug_tools.spl`
  - target: 85%+ minimum, higher where practical
- `src/app/mcp/main_lazy_debug_log_tools.spl`
  - target: 90%+
- `src/app/mcp/main_lazy_tasks.spl`
  - target: 90%+
- `src/app/mcp/main_lazy_test_daemon_tools.spl`
  - target: 85%+ minimum

### Completeness Gates

- 100% of visible CLI commands classified
- 100% of listed MCP tools classified
- 100% of listed MCP tools dispatch-checked
- 0 user-visible placeholder CLI commands

## Implementation Waves

### Wave 1: Inventory and Truthfulness

- build command/tool inventories
- classify visible surfaces
- remove or hide placeholder CLI commands from help
- add failing tests for inventory drift

### Wave 2: Placeholder Elimination

- implement or reclassify `verify`, `migrate`, `diff`, `constr`
- harden wrapper command behavior
- align CLI help and docs

### Wave 3: MCP Family Hardening

- classify all MCP tools
- add dispatch/schema parity tests
- add wrapper maturity labeling and tests

### Wave 4: Protocol and System Depth

- expand stdio/protocol integration tests
- add system matrix tests for CLI and MCP families
- add docs/help consistency tests

### Wave 5: Coverage Enforcement and Cleanup

- enforce package coverage thresholds
- clean dead/inaccurate docs
- generate final completeness report

## Risks

- Some CLI commands may intentionally be placeholders for planned subsystems; if
  so, visibility decisions must be made before implementation starts.
- Some MCP tools rely on shelling out to the `simple` binary, which can create
  recursive behavior or wrapper fragility if not clearly bounded.
- Tool count and command count can drift quickly unless inventories are derived
  or test-generated.
- Debug/test-daemon families are harder to exercise comprehensively without
  careful deterministic seams.

## Exit Criteria

This plan is complete when:

- `simple --help` contains no misleading placeholder commands
- the CLI command surface is classified and tested
- `simple-mcp` listed tools are all dispatch-verified and classified
- CLI/MCP differences are documented rather than implicit
- protocol, family, and system test coverage exists for all major surfaces
- package coverage targets are met or explicitly justified
