# T32 MCP: CLI, Async, Blocking CMM, and Window UX Research

_Date:_ 2026-03-25

## Summary

This document answers four design questions for the TRACE32 MCP server in this repo:

1. Should the server stay CLI-first, or move away from CLI-style packaging?
2. Should the MCP layer be synchronous, partially async, or fully async?
3. How should headless MCP handle interactive/blocking CMM scripts?
4. How should TRACE32 windows, status, and state changes be surfaced to an LLM user?

Primary recommendation:

- Keep the server CLI-first. That is the dominant packaging pattern for local MCP servers today.
- Keep `MCP 2025-06-18` as the main compatibility target.
- Make only long-running T32 operations async in phase 1.
- Represent async work in current MCP as server-managed jobs plus polling/resources.
- Treat native MCP Tasks support from `2025-11-25` as a phase-2 upgrade path, not the base design.
- Do not try to fully auto-convert interactive CMM into headless-safe CLI scripts. Provide validator-assisted manual conversion guidance instead.
- Add server-side window snapshot storage and diff-aware responses so Claude sees concise state changes first and full windows on demand.

## What Changed in the MCP Ecosystem

### CLI-first MCP is normal, not a workaround

Local MCP servers are commonly distributed as normal executables with a stdio subcommand or direct stdio entrypoint.

Examples from maintained official projects:

- GitHub's official MCP server can be built as a local binary and configured with `github-mcp-server stdio`; the same binary also exposes CLI utility subcommands for search/debugging.[1]
- Salesforce's DX MCP server is run through `npx @salesforce/mcp ...`, with CLI flags controlling org scope, toolsets, logging, and dynamic tool loading.[2]
- Anthropic exposes Claude Code itself as an MCP server via `claude mcp serve`.[3]

Implication for this repo:

- `bin/t32_mcp_server` and `bin/t32_lsp_mcp_server` already fit the mainstream MCP packaging model.
- A separate interactive `t32-cli` is still useful, but it should share the same backend/session model as MCP rather than define a separate product direction.

### Current MCP still centers on request/response tools

The current protocol version is `2025-06-18`.[4] In this version:

- tools are request/response
- tools can return `content`, `structuredContent`, `resource_link`, and embedded resources
- tools may provide `outputSchema`
- tools may provide annotations such as `readOnlyHint`, `destructiveHint`, `idempotentHint`, and `openWorldHint`.[5]

That is enough to build a good user experience for T32 today:

- return concise text for the assistant/user
- return stable `structuredContent` for parsing
- move large or full window payloads into resources

### True task objects are newer and still experimental

`2025-11-25` introduces Tasks and progress utilities, but Tasks are explicitly marked experimental.[6][7] They are a good future fit for long-running flashing, run-control, or trace collection, but they are not the safest base dependency for the current server.

Implication:

- do not block the redesign on upgrading the server protocol
- build an internal job abstraction now
- map that abstraction to current MCP tools/resources first
- later expose it through MCP Tasks when client support is strong enough

### Claude Code already rewards concise MCP output

Anthropic's MCP docs note that Claude Code automatically exposes MCP resource list/read tools when the server supports resources.[3] The same docs also document output warnings around large MCP tool outputs: warning threshold at 10,000 tokens and default cap 25,000 tokens via `MAX_MCP_OUTPUT_TOKENS`.[3]

Implication:

- window dumps should not always be returned inline from a tool
- the server should prefer summaries and diffs in tool responses
- full window content should remain available through explicit resource reads or explicit full-capture requests

## Current Repo State

The current server already has a solid base:

- `examples/10_tooling/trace32_tools/t32_mcp/main.spl` is a stdio MCP server on `MCP 2025-06-18`
- `session_tools.spl` already blocks obvious headless-unfriendly PRACTICE commands such as `DIALOG.*`, `INKEY`, `ENTER`, `PAUSE`, `STOP`, and `SCREEN.WAIT`
- `t32_cmm_run` already supports `wait=true` and polls `PRACTICE.STATE()`
- `window_tools.spl` already captures text via `WinPrint.*` and falls back to `PRinTer.FILE`
- resources are already implemented
- tool annotations are already emitted

Gaps relative to the desired UX:

- no first-class async job model
- no explicit separation between tool wait timeout and background execution lifetime
- no persistent snapshot model for window diffs
- no policy for when to show summary vs diff vs full window content
- no structured connect/status payload for run/stop/system state
- current CMM blocking handling is mostly static detection plus `force`, not a conversion guide

## TRACE32 Findings Relevant to Headless MCP

### Interactive PRACTICE commands are genuinely blocking

Lauterbach's docs are explicit:

- `INKEY` waits for a keystroke and can stop script execution until a key is pressed.[8]
- `ENTER` is window-based input through an AREA window.[9]
- `SCREEN.WAIT` halts PRACTICE execution until the window data has been processed.[9][8]
- `STOP` interrupts the PRACTICE script and leaves it resumable by `CONTinue`.[8]
- Lauterbach training material shows dialog behavior becoming modal when paired with `STOP`.[10]

This validates the repo's current blocking classification. It should be expanded, not removed.

### AREA is the correct text channel for headless I/O

Lauterbach documents that:

- input/output can be routed through AREA windows
- print operations go to the TRACE32 message line
- AREA windows can be created, selected, displayed, and saved
- `AREA.Select` governs where `PRINT` and `ENTER` operate.[9][11]

That means the correct headless-safe pattern is:

- use macros/`ENTRY` for input values
- use `PRINT` plus `AREA` for textual output
- use `WinPrint.AREA` or `PRinTer.FILE` for capture

### Window capture through WinPrint/PRinTer is officially supported

Lauterbach documents:

- `PRinTer.FILE` reroutes printer output to a file
- `WinPrint.<command>` sends a window's contents to the selected output target
- `PRinTer.FILE` auto-closes after the print operation
- `SCREEN.WAIT` is sometimes required before printing asynchronously generated window content.[12]

This confirms the repo's current `WinPrint.*` plus `PRinTer.FILE` strategy is the right base.

### Run/stop state is capturable

Lauterbach documentation shows:

- `STATE.RUN()` returns true while the program is running and false when stopped.[13]
- `WAIT !STATE.RUN()` is a standard script idiom for waiting until the target stops.[8]
- `SYStem.state` displays a system-status window with debugger/target settings and state-related links.[14]

This is enough to build a compact status model for MCP:

- `running | stopped | unknown`
- optional system-state window text
- optional status/message line text where capturable

### Do not build the UX around scraping GUI chrome

The TRACE32 GUI has a message line and dialog-style windows, but those are poor primary interfaces for MCP. The stable MCP-facing status model should come from explicit commands and captured windows, not from trying to scrape transient GUI chrome.

Recommended priority order:

1. explicit state queries such as `STATE.RUN()` and command success/failure
2. `SYStem.state` or other capturable status windows
3. AREA-based textual output emitted by scripts
4. message-line text if there is a reliable documented way to capture it

Practical conclusion:

- show `running/stopped` from a stable query, not inferred from GUI paint state
- show connection success/error from the session open result itself
- show script status from structured MCP fields plus captured AREA output
- treat raw status-bar scraping as optional and low priority

## Recommendation: Keep the Server Partially Async

### Why not fully synchronous

Fully synchronous behavior is poor for:

- flash/program operations
- long script execution
- target run/until-break workflows
- trace collection
- operations that depend on target timing or external stimulus

Even with timeouts, a pure sync design forces the MCP client to wait on operations whose useful state can be reported incrementally.

### Why not fully async everywhere

Making everything async would degrade simple workflows:

- `t32_eval`
- `t32_field_get`
- `t32_field_set`
- `t32_window_capture`
- `t32_window_list`
- `t32_resources_list`
- `t32_resource_read`

These should remain immediate. Returning a job id for trivial reads would slow the user and make tool use harder for the LLM.

### Recommended split

Keep these synchronous:

- session open/resume/close
- core list/select
- eval
- field get/set
- action invoke when the command is immediate
- window open/list/describe
- window capture by default
- area read
- resources list/read

Support async mode for:

- `t32_cmd_run` when command class is long-running
- `t32_cmm_run` when script may outlive the tool call
- screenshot capture if it becomes slow or fragile
- future trace/coverage/flash collection tools

Recommended rule:

- each eligible tool gets `wait`, `timeout_ms`, and `background`
- `background=true` returns immediately with a job
- `wait=true` waits up to `timeout_ms` for completion
- if neither is set, use tool-specific defaults

## Async in Current MCP 2025-06-18

### Recommended phase-1 model

Add an internal job manager in the T32 server and expose it with normal tools/resources.

Recommended new surface:

- `t32_job_list()`
- `t32_job_get(job_id)`
- `t32_job_cancel(job_id)` if the backend can interrupt safely
- `t32_job_result(job_id)` or resource reads under `t32://jobs/<id>`

Recommended job fields:

- `job_id`
- `tool_name`
- `session_id`
- `core_id`
- `status` = `queued | running | waiting_target | waiting_practice | completed | failed | timed_out | cancelled`
- `started_at`
- `updated_at`
- `timeout_ms`
- `summary`
- `result_available`
- `result_resource_uri`
- `error`

Recommended tool response shape for a background launch:

- human text summary in `content`
- machine fields in `structuredContent`
- optional `resource_link` to `t32://jobs/<id>`

Why this fits the spec:

- tools in `2025-06-18` can return `structuredContent` and resource links.[5]
- Claude Code can already list and read resources.[3]

### Channels are optional, not the primary async design

Claude Code supports channel-style push messages from MCP servers.[3] That is useful for external event streams, but it is not the best phase-1 design for T32 command completion.

Recommended use:

- phase 1: polling plus resources for job state/result
- optional later use of channels for watched-window changes or external target events
- do not require channels for ordinary command/script completion

Reason:

- jobs already have a natural poll/read lifecycle
- pull-based state is easier to reason about for debugging and replay
- channels add another delivery model and another failure mode
- the server should work well even in clients that do not use channel push heavily

### Future appendix: map the same model to MCP Tasks

When the server upgrades to `2025-11-25`, the same internal job manager can back:

- task-backed tool requests
- progress notifications
- `tasks/get`
- `tasks/list`
- `tasks/cancel`
- deferred result retrieval

This should be a protocol adapter step, not a redesign.

## Timeout Policy

### Recommendation

Every potentially blocking operation should have both:

- a server default timeout
- a per-call override

Timeouts should be explicit in result fields, not only embedded in prose.

Recommended timeout classes:

- `connect_timeout_ms`
- `command_timeout_ms`
- `practice_wait_timeout_ms`
- `window_capture_timeout_ms`
- `job_retention_ms`

Recommended defaults:

- connect/open session: 5,000 to 10,000 ms
- quick command/eval/window read: 5,000 ms
- CMM foreground wait: 30,000 ms
- flash/program/trace jobs: background by default, job timeout 5 to 15 minutes depending on tool

Behavior:

- foreground timeout should not imply the underlying job is dead if it is intentionally running in background
- timed out foreground waits should return `status=running` plus `job_id` when background continuation is possible
- only backend termination should return `timed_out` terminal status

## Blocking CMM: Preventing Headless Hangs

### Recommended policy

Keep three classes:

- `BLOCK`: must not run in headless MCP unless `force=true`
- `WARN`: allowed, but may stall or produce poor UX
- `INFO`: safe, but behavior differs in headless mode

Recommended `BLOCK` set:

- `DIALOG.OK`
- `DIALOG.YESNO`
- `DIALOG.FILE`
- `DIALOG.DIR`
- `DIALOG.STRING`
- `INKEY`
- `ENTER`
- `PAUSE`
- `STOP`
- `SCREEN.WAIT` without an explicit CLI-safe purpose

Recommended `WARN` set:

- unbounded `WAIT`
- menu-driving commands
- editor/window commands whose output is not later captured

### Do not promise automatic conversion

Automatic conversion is risky because interactive CMM often encodes real control flow:

- user confirmations
- path selection
- pause/resume breakpoints
- timing and wait assumptions

Recommended product stance:

- validator-assisted manual conversion
- pattern-based suggestions
- optional boilerplate generation for safe wrappers
- no silent semantic rewrite

### Manual conversion cookbook

Recommended rewrite patterns:

1. Replace user input with script parameters.
   - Use `ENTRY &arg1 &arg2`
   - Pass values from MCP tool arguments or wrapper-generated macros

2. Replace dialogs with explicit values.
   - `DIALOG.FILE` -> tool argument `path`
   - `DIALOG.YESNO` -> tool argument `confirm=true|false`
   - `DIALOG.STRING` -> tool argument `value`

3. Replace pauses with logged checkpoints.
   - `PAUSE` or `ENTER` -> `PRINT "checkpoint: ..."` plus conditional branching from passed flags

4. Bound waits.
   - `WAIT <condition>` -> loop or wait pattern with explicit timeout and clear timeout message

5. Route output to AREA.
   - ensure `AREA.Create`, `AREA.Select`, and `PRINT`
   - capture via `WinPrint.AREA` or printer file fallback

6. Avoid display-only dependencies.
   - do not rely on `WINPOS`, `SCREEN.ON`, or modal dialog windows as execution steps

### Example guidance

Unsafe interactive pattern:

```cmm
PRINT "Set the PC value"
ENTER &pc
Register.Set pc &pc
```

CLI-safe pattern:

```cmm
ENTRY &pc
IF "&pc"==""
(
  PRINT %ERROR "missing parameter: pc"
  ENDDO
)
Register.Set pc &pc
PRINT "pc set to " &pc
```

Unsafe confirmation pattern:

```cmm
DIALOG.YESNO "Erase flash?"
FLASH.Erase
```

CLI-safe pattern:

```cmm
ENTRY &confirm
IF "&confirm"!="true"
(
  PRINT "flash erase skipped"
  ENDDO
)
FLASH.Erase
PRINT "flash erase requested"
```

## CMM Converter and Validator Recommendation

Use a two-layer design:

1. Validator
   - detect blocking commands
   - detect likely display-only commands
   - detect unbounded waits
   - detect missing parameterization opportunities
   - classify script as `safe`, `needs_manual_rewrite`, or `unsafe_for_headless`

2. Assisted conversion guide
   - generate a report with suggested rewrites
   - optionally generate a wrapper template that calls the original script with `ENTRY` parameters where possible

What should not be auto-rewritten:

- nested dialog-driven flows
- scripts whose semantics depend on user timing
- scripts using modal editor/debug windows as checkpoints

This matches the existing `cmm_validate_cli` direction: validation is credible; semantic auto-conversion is not yet trustworthy enough.

## Window and Status UX for Claude

### What the user should see by default

For most tool calls, return:

- a one-line status summary
- relevant state changes
- compact changed window data if available
- a link/resource path for full content

Do not dump full windows by default after every command.

### Recommended connect/open-session result

On successful connection, return structured fields:

- `session_id`
- `host`
- `port`
- `backend`
- `intercom_name`
- `connected=true`
- `run_state`
- `status_summary`
- `message_line` if available

On failure, return:

- `connected=false`
- `error_code`
- `error_message`
- `backend_attempts`

### Window snapshot model

The MCP server should keep in-memory snapshot state per session/core/window:

- `window_key`
- `title`
- `last_capture_at`
- `last_content`
- `last_structured_rows` if parseable
- `last_hash`

Recommended behavior:

- first capture of a window returns full content
- later captures return:
  - `changed=false` if identical
  - `changed=true` plus `window_diff` if changed
- if parsing fails or layout changed materially, return full content again

### Diff strategy

Use a layered diff:

1. Structured row diff when the window is label/value shaped.
   - example: register windows, status lines, named fields
   - emit `label`, `old`, `new`

2. Table/cell diff when the window is grid-like.
   - emit changed cell plus row/column context or surrounding line block

3. Fallback text diff.
   - small surrounding context only

Recommended response fields:

- `window`
- `title`
- `changed`
- `change_count`
- `window_diff`
- `content_preview`
- `full_resource_uri`

### When to show full windows

Return full window content only when:

- user explicitly asks for full content
- first capture after opening/switching window
- diff confidence is low
- window changed too broadly for a useful diff

### Quiet switching

Recommended meaning:

- session/core switches should update internal focus only
- they should not automatically emit full window contents
- optional watched windows can be refreshed silently and only report if changed

This gives better LLM UX than unconditional dumps after every switch.

## Should MCP "Show the Window" to the User?

Not literally. MCP can return text, resources, and links. It cannot force Claude Code to open a TRACE32 GUI window for the end user in the chat UI.

What works well:

- return the window title
- return concise changed values
- expose full captured text as a resource
- let Claude summarize or quote the relevant parts for the user

This is the right abstraction boundary:

- TRACE32 GUI remains the real GUI
- MCP exposes a text/resource representation of GUI state

## Suggested Changes to the T32 MCP Interface

Recommended additions:

- job tools/resources for async execution
- a `t32_status_snapshot` tool
- optional `watch=true` or `diff=true` parameters on window capture
- explicit timeout parameters named `*_timeout_ms`
- structured connect/result payloads

Recommended additions to `t32_window_capture`:

- `mode=summary|diff|full`
- `since_last=true|false`
- `include_resource=true|false`

Recommended additions to `t32_cmm_run`:

- `background=true|false`
- `wait=true|false`
- `timeout_ms`
- `capture_area=true|false`
- `cli_safe=true|false` to request strict blocking enforcement

Recommended additions to `t32_cmd_run`:

- same async/timeout flags
- command classification in the result: `immediate`, `interactive_blocked`, `long_running`, `background_job`

## Best User Experience Choice

Best overall choice for this repo:

- partially async MCP
- current-spec compatible
- diff-aware windows
- resource-backed full payloads
- strict blocking prevention for headless CMM
- validator-assisted manual conversion

This gives the best balance of:

- compatibility with today's clients
- low cognitive load for the LLM
- fewer hangs
- better large-output handling
- clean migration path to future MCP Tasks support

## Phased Implementation Roadmap

### Phase 1

- add internal job manager
- add sync/async split to `t32_cmd_run` and `t32_cmm_run`
- add explicit timeout fields and config defaults
- add `t32_status_snapshot`
- add window snapshot store and `mode=summary|diff|full`
- add resources for full window content and job results

### Phase 2

- strengthen `cmm_validate_cli` to emit a conversion report and severity classes
- add wrapper-template generation for parameterized scripts
- add optional watched-window refresh policy

### Phase 3

- upgrade protocol layer for `2025-11-25` Tasks when client support is acceptable
- map internal jobs to Tasks/progress/cancel without changing tool semantics

## Sources

[1] GitHub MCP Server README, local binary + `stdio`, CLI utilities, toolset control, and description overrides: https://github.com/github/github-mcp-server

[2] Salesforce DX MCP Server docs, CLI flags, toolsets, dynamic tools, and Claude Code config: https://github.com/salesforcecli/mcp

[3] Anthropic Claude Code MCP docs, resource support and MCP output limits: https://docs.anthropic.com/en/docs/claude-code/mcp

[4] MCP versioning/spec index showing current protocol version `2025-06-18`: https://modelcontextprotocol.io/specification/

[5] MCP `2025-06-18` tools spec, tool metadata, annotations, structured content, output schema, and resource links: https://modelcontextprotocol.io/specification/2025-06-18/server/tools

[6] MCP `2025-11-25` Tasks utility, explicitly experimental: https://modelcontextprotocol.io/specification/2025-11-25/basic/utilities/tasks

[7] MCP `2025-11-25` progress utility: https://modelcontextprotocol.io/specification/2025-11-25/basic/utilities/progress

[8] Lauterbach PRACTICE Script Language Reference Guide, `INKEY`, `SCREEN.WAIT`, `STOP`, and `WAIT !STATE.RUN()`: https://www2.lauterbach.com/pdf/practice_ref.pdf

[9] Lauterbach PRACTICE Script Language User's Guide, AREA I/O, `ENTER`, `INKEY`, `SCREEN.OFF`, `SCREEN.WAIT`: https://www2.lauterbach.com/pdf/practice_user.pdf

[10] Lauterbach Training Script Language PRACTICE, modal dialog behavior via `STOP`: https://www2.lauterbach.com/pdf/training_practice.pdf

[11] Lauterbach PowerView Command Reference, `AREA.view`, `AREA.Select`, and AREA I/O behavior: https://www2.lauterbach.com/pdf/ide_ref.pdf

[12] Lauterbach PowerView Command Reference, `PRinTer.FILE`, `WinPrint.*`, and print-to-file behavior: https://www2.lauterbach.com/pdf/ide_ref.pdf

[13] Lauterbach training material excerpt documenting `STATE.RUN()`: https://www2.lauterbach.com/pdf/training_practice.pdf

[14] Lauterbach debugger documentation and PowerView docs covering `SYStem.state`: https://www2.lauterbach.com/pdf/debugger_armv8v9.pdf
