# MCP Scenario Manual Quality Plan

**Date:** 2026-05-30
**Status:** In progress
**Parent plan:** `doc/03_plan/sspec_scenario_manual_capture_plan.md`

## Purpose

Make MCP generated SPipe documentation the exemplar for scenario-based manuals.
The current MCP specs already test important behavior, but generated docs still
read like test inventories or raw protocol matrices. The target is an
operator-readable manual: start the MCP server, initialize the protocol, list
tools, call safe tools, inspect errors, and diagnose failures with protocol and
execution evidence attached to each step.

## Current MCP Spec Classes

| Spec area | Manual role | Default visibility |
|---|---|---|
| `test/02_integration/app/mcp_stdio_integration_spec.spl` | Primary operator flow for stdio MCP server behavior | `show` |
| `test/03_system/feature/app/mcp_protocol_runtime_spec.spl` | Protocol capability matrix in one session | `folded` until split into user flows |
| `test/03_system/feature/app/mcp_cli_passthrough_diag_spec.spl` | Diagnostic regression flow | `show` for one primary diagnostic, `folded` for variants |
| `test/03_system/feature/app/mcp_protocol_gap_matrix_spec.spl` | Compliance inventory and plan locks | `folded` / `detail` |
| `test/02_integration/app/app_mcp_intensive_spec.spl` | Stress/intensive loops and matrix checks | `folded` by default |
| skipped OOM specs such as `mcp_debug_log_spec.spl` | Known blocked capability docs | `detail` with reason, not primary manual |

## Target Manual Example

The generated MCP stdio manual should eventually read like this:

```markdown
#### Operator verifies the MCP stdio server

1. Operator sends an initialize request.

   Protocol capture
   - request: `initialize`
   - protocolVersion: `2025-06-18`
   - response: `serverInfo.name = simple-mcp-full`

2. Operator sends the initialized notification and lists tools.

   Protocol capture
   - request: `tools/list`
   - response includes `debug_create_session`
   - response has no top-level JSON-RPC error

3. Operator calls an unknown tool to verify tool-level errors.

   Protocol capture
   - request: `tools/call no_such_tool`
   - response: `isError = true`
   - top-level JSON-RPC error is absent

4. Operator opens and reads a file through the safe editor MCP subset.

   API/protocol capture
   - advertised: `editor.open_file`, `editor.read_buffer`,
     `editor.list_open_files`
   - not advertised: `editor.edit`, `editor.search`, `editor.diagnostics`
   - response contains the opened file path and content

<details>
<summary>Executable SPipe</summary>

...

</details>
```

The generated page should not lead with a bullet list of `it` titles or raw
input string construction. Those belong in folded executable/detail sections.

## Required Authoring Changes

The first authoring pass is applied to
`test/02_integration/app/mcp_stdio_integration_spec.spl` with executable-safe
comment metadata:

- The initialize request scenario is `# @inline` and `# @capture(protocol)`.
- Tool listing and unknown-tool scenarios use `# @prev(...)` and protocol
  capture.
- The safe editor subset scenario uses the tool-list scenario as previous
  context and API capture.
- The scoped-argument regression is `# @manual: folded` because it is useful
  diagnostic detail, not the primary manual path.
- Starter operator `# @step` labels now mark the initialize, tools/list,
  unknown-tool, safe editor, and scoped-argument actions so generated docs lead
  with manual prose before the folded executable source.

Future specs should follow the same pattern. When docgen supports executable
annotations everywhere, update MCP specs as follows:

```simple
@inline
it "MCP server is initialized":
    operator.send_initialize()

@prev("MCP server is initialized")
@capture(protocol)
it "operator lists MCP tools":
    operator.send_initialized()
    operator.list_tools()
    Then_tools_include_debug_session()

@prev("MCP server is initialized")
@capture(protocol)
it "operator sees tool-level error for unknown tool":
    operator.call_unknown_tool()
    Then_unknown_tool_is_tool_error()
```

Until annotation metadata is executable everywhere, use implemented comment
metadata for visibility:

```simple
# @manual: folded
it "tracks complete debug tool set":
    ...

# @manual: skip
it "checks generated helper plumbing":
    ...

# @inline
it "MCP server is initialized":
    ...
```

Helper/checker targets:

- `send_initialize` -> step text "Operator sends an initialize request".
- `send_initialized` -> step text "Operator sends the initialized notification".
- `list_tools` -> step text "Operator lists MCP tools".
- `call_unknown_tool` -> step text "Operator calls an unknown tool".
- `Then_*` checkers emit both assertions and protocol evidence summaries.

## Capture Requirements

MCP capture should primarily use `protocol`, `api`, `exec`, `text`, and `log`
kinds:

- `protocol`: JSON-RPC request method, id, params summary, response result/error
  summary, and redacted body preview.
- `api`: tool name, arguments, structured content summary, `isError`.
- `exec`: command used to launch `bin/simple_mcp_server`, stdin framing mode,
  stdout/stderr snippets, exit code.
- `log`: startup/log-mode output for diagnostic scenarios.
- `text`: generated helper output when the protocol body is too large.

Do not use screenshot/TUI capture for MCP unless the scenario is explicitly
about an MCP-backed UI surface.

## Manual Review Checklist

- [x] The generated doc opens with the primary MCP scenario, not a matrix.
- [x] The scenario summary matrix follows the generated scenario body instead
      of appearing before the operator flow.
- [x] Setup flows are expanded into steps and do not print redundant
      `Previous:` metadata.
- [x] Boolean assertion summaries render as expected-result bullets under the
      step that produced them.
- [x] Escaped JSON assertion fragments are normalized in expected-result
      bullets.
- [x] Step capture labels are typed as Protocol/API/TUI/etc. instead of a
      generic `Capture:` prefix.
- [x] Captured protocol/API steps include compact evidence previews derived
      from generated expected checks.
- [x] Folded executable blocks show runnable source line counts.
- [x] Long expected-value snippets are truncated and point to folded executable
      source.
- [x] Protocol/API/exec captures appear under the step that produced them.
- [x] Long JSON payloads are summarized, with full payload folded or linked.
- [x] Intensive loops, matrix locks, schema inventories, and OOM-skip details
      are folded by default.
- [x] The manual can be used to reproduce the scenario without opening the
      source test file.

## Implementation Dependency

This plan depends on the feature requests in
`doc/08_tracking/feature/sspec_scenario_manual_requests.md`, especially:

- `FR-SSPEC-MANUAL-0001` for step/inline/previous scenario metadata.
- `FR-SSPEC-MANUAL-0002` for typed protocol/API/exec evidence.
- `FR-SSPEC-MANUAL-0003` for shared checker/capture helpers.
- `FR-SSPEC-MANUAL-0004` for the repo-wide manual uplift.
