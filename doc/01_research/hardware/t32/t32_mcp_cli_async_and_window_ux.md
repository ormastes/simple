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

## CLI-to-MCP Tool Mapping

### Full Mapping Table

| # | CLI Command | CLI Subcommand | MCP Tool | Status | Notes |
|---|-------------|----------------|----------|--------|-------|
| 1 | `sessions` | `list` | `t32_sessions_list` | Mapped | Both list all open sessions |
| 2 | `sessions` | `open` | `t32_session_open` | Mapped | Both create a new connection to a T32 instance |
| 3 | `sessions` | `close` | `t32_session_close` | Mapped | Both tear down and remove a session |
| 4 | `sessions` | `use` | `t32_session_resume` | Mapped (different name) | CLI `use` and MCP `resume` both switch the active session |
| 5 | `sessions` | `info` | -- | CLI-only | Prints detailed session info; no MCP equivalent |
| 6 | `cores` | `list` | `t32_core_list` | Mapped | Both enumerate cores in the current session |
| 7 | `cores` | `select` | `t32_core_select` | Mapped | Both switch the active core |
| 8 | `windows` | `list` | `t32_window_list` | Mapped | Both list available windows from the catalog |
| 9 | `window` | `show` | `t32_window_capture` | Mapped (different name) | CLI `show` displays content; MCP `capture` returns text |
| 10 | `window` | `open` | `t32_window_open` | Mapped | Both issue the T32 command to open a window |
| 11 | `window` | `describe` | `t32_window_describe` | Mapped | Both return window metadata (actions, fields, help) |
| 12 | `field` | `get` | `t32_field_get` | Mapped | Both read a field value |
| 13 | `field` | `set` | `t32_field_set` | Mapped | Both write a field value |
| 14 | `action` | `do` | `t32_action_invoke` | Mapped | Both execute a cataloged action |
| 15 | `action` | `list` | -- | CLI-only | Lists all actions; no MCP equivalent |
| 16 | `screenshot` | _(no sub)_ | `t32_screenshot` | Mapped | Both capture a window as an image file |
| 17 | `cmm` | _(no sub)_ | `t32_cmm_run` | Mapped | CLI runs CMM path; MCP runs content or path with wait/timeout |
| 18 | `shell` | _(no sub)_ | -- | CLI-only | Interactive REPL; no MCP equivalent (by design) |
| 19 | -- | -- | `t32_cmd_run` | MCP-only | Run a single raw PRACTICE command with blocking detection |
| 20 | -- | -- | `t32_eval` | MCP-only | Evaluate a T32 expression via `EVAL` |
| 21 | -- | -- | `t32_history_tail` | MCP-only | Return last N entries from in-memory command history |
| 22 | -- | -- | `t32_resources_list` | MCP-only | List MCP resources (`t32:///sessions`, `t32:///windows`, etc.) |
| 23 | -- | -- | `t32_resource_read` | MCP-only | Read a single MCP resource by URI |
| 24 | -- | -- | `t32_setup_headless` | MCP-only | Configure headless mode: `SCREEN.OFF`, AREA, semihost |
| 25 | -- | -- | `t32_area_read` | MCP-only | Read/clear AREA buffer via `WinPrint.AREA` |
| 26 | -- | -- | `t32_cmm_commands` | MCP-only | Query built-in CMM command database by group/search |

**Totals:** 18 mapped pairs, 9 MCP-only tools, 3 CLI-only features (plus `sessions use` vs `session_resume` naming difference).

### MCP-Only Tools Analysis (9)

**`t32_cmd_run`** — Runs a single raw PRACTICE command with blocking-pattern detection and `force` override. CLI delegates to `cmm` for scripts and `action do` for catalog actions. Adding `t32-cli cmd <command>` would close this gap.

**`t32_eval`** — Evaluates T32 expressions (e.g., `Register(PC)`, `PRACTICE.STATE()`). Essential for LLM state inspection without full scripts. CLI has no `eval` subcommand; the shell REPL could be extended.

**`t32_history_tail`** — Returns structured command history. CLI shell has display-only `history` in REPL but no batch subcommand.

**`t32_resources_list` / `t32_resource_read`** — MCP protocol primitives (session manifest, window catalog, history as resources). No CLI analog needed.

**`t32_setup_headless`** — Configures headless mode (`SCREEN.OFF`, AREA creation, semihost). MCP-specific by design; CLI users have a display.

**`t32_area_read`** — Reads AREA buffer for headless script output. CLI users see AREA in the GUI directly.

**`t32_cmm_commands`** — LLM-accessible CMM command reference (120+ commands by group/search). CLI users consult Lauterbach manuals.

### CLI-Only Features Analysis (3)

**`sessions info`** — Detailed single-session view. MCP `t32_sessions_list` returns summaries for all sessions. Recommendation: add `t32_session_info` tool or extend `t32_sessions_list` with optional `session_id` filter.

**`action list`** — Lists all cataloged actions. MCP `t32_action_invoke` requires the caller to know the action key. Recommendation: add `t32_action_list` tool (or fold into `t32_window_describe`).

**`shell` (REPL)** — Interactive loop with readline. Cannot map to stateless MCP. No equivalent needed; the LLM achieves the same workflow by calling individual tools.

### Recommendations for Closing Gaps

**High priority (LLM agent workflow):**
1. Add `t32_session_info` MCP tool — avoid parsing full session list to inspect one session
2. Add `t32_action_list` MCP tool — let LLM discover available actions before invoking
3. Add CLI `cmd` subcommand — mirror `t32_cmd_run` for batch CLI
4. Add CLI `eval` subcommand — mirror `t32_eval`

**Medium priority (symmetry):**
5. Add CLI `history` batch subcommand
6. Extend `t32_sessions_list` with optional `session_id` parameter

**Low priority (MCP-native, no CLI analog needed):**
7. `t32_resources_list/read` — protocol primitives
8. `t32_setup_headless` — MCP-specific by design
9. `t32_area_read` / `t32_cmm_commands` — headless/LLM assistance

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

## Job Manager Architecture

This section expands the brief phase-1 job model into a concrete architecture with class design, storage model, integration points, polling strategy, and migration path.

### Design context

The main MCP server (`src/app/mcp/main_lazy_tasks.spl`) already implements background task management via a `BackgroundTask` class, `BG_TASKS` array, process spawning, and "working"/"completed"/"failed" lifecycle. The T32 MCP server is fully synchronous today: `t32_cmm_run` with `wait=true` polls `PRACTICE.STATE()` in a blocking loop (500ms intervals in the MCP handler, 200ms in the library runner), and all other tools block until the T32 remote API call returns.

The job manager described here is T32-specific. It manages in-process polling state tied to T32 sessions and cores rather than spawning subprocesses.

### T32Job class

```simple
class T32Job:
    job_id: text                  # "j1", "j2", ... monotonic
    tool_name: text               # "t32_cmm_run", "t32_cmd_run", etc.
    session_id: text              # which McpT32Session owns this job
    core_id: text                 # which core was selected at launch
    status: text                  # state machine value (see below)
    started_at: i64               # unix microseconds
    updated_at: i64               # unix microseconds, refreshed on every poll
    timeout_ms: i64               # max background lifetime; 0 = no limit
    poll_interval_ms: i64         # how often the server should poll T32
    summary: text                 # human-readable one-liner
    result: text                  # captured output (AREA text, command output)
    error: text                   # error message if failed/timed_out
    resource_uri: text            # "t32:///jobs/j1" for resource reads
    # internal fields (not exposed in tool responses)
    _script_path: text            # CMM script path for cmm_run jobs
    _command: text                # raw command for cmd_run jobs
    _last_practice_state: text    # last PRACTICE.STATE() value
    _area_name: text              # AREA window to capture on completion
```

### Status state machine

```
queued ──────> running ──────> completed
                 │                 ▲
                 ├──> waiting_target ──┤  (target running, waiting for stop)
                 │                     │
                 ├──> waiting_practice ─┤  (PRACTICE script still executing)
                 │
                 ├──> failed           (T32 error or command failure)
                 ├──> timed_out        (backend termination after timeout_ms)
                 └──> cancelled        (client requested cancel)
```

Terminal states: `completed`, `failed`, `timed_out`, `cancelled`.

Transition rules:

- `queued` -> `running`: job manager sends the command/script to T32 and gets acknowledgement.
- `running` -> `waiting_practice`: first poll of `PRACTICE.STATE()` returns non-zero (script executing).
- `running` -> `waiting_target`: `STATE.RUN()` returns true (target is running, job waits for stop).
- `waiting_practice` -> `completed`: `PRACTICE.STATE()` returns 0 (idle).
- `waiting_practice` -> `failed`: `PRACTICE.STATE()` returns "dialog" or error.
- `waiting_target` -> `completed`: `STATE.RUN()` returns false (target stopped).
- any non-terminal -> `timed_out`: `updated_at - started_at > timeout_ms` and `timeout_ms > 0`.
- any non-terminal -> `cancelled`: client calls `t32_job_cancel`.

### T32JobManager class

```simple
var T32_JOBS: [T32Job] = []
var T32_NEXT_JOB_ID: i64 = 1
val T32_MAX_CONCURRENT_JOBS: i64 = 16
val T32_JOB_RETENTION_MS: i64 = 300000   # 5 minutes for completed jobs
val T32_DEFAULT_POLL_MS: i64 = 500

class T32JobManager:
    # No instance fields — operates on module-level state.
    # This matches the existing MCP pattern (BG_TASKS is module-level).

    static fn create_job(tool_name: text, session_id: text, core_id: text,
                         timeout_ms: i64) -> Result<T32Job, text>:
        val active = T32JobManager.count_active()
        if active >= T32_MAX_CONCURRENT_JOBS:
            return Err("max concurrent jobs ({T32_MAX_CONCURRENT_JOBS}) reached")

        val jid = "j" + str(T32_NEXT_JOB_ID)
        T32_NEXT_JOB_ID = T32_NEXT_JOB_ID + 1
        val now = rt_time_now_unix_micros()

        var job = T32Job(
            job_id: jid,
            tool_name: tool_name,
            session_id: session_id,
            core_id: core_id,
            status: "queued",
            started_at: now,
            updated_at: now,
            timeout_ms: timeout_ms,
            poll_interval_ms: T32_DEFAULT_POLL_MS,
            summary: "",
            result: "",
            error: "",
            resource_uri: "t32:///jobs/" + jid,
            _script_path: "",
            _command: "",
            _last_practice_state: "",
            _area_name: ""
        )
        T32_JOBS = T32_JOBS + [job]
        Ok(job)

    static fn get_job(job_id: text) -> Option<T32Job>:
        for job in T32_JOBS:
            if job.job_id == job_id:
                return Some(job)
        nil

    static fn list_jobs() -> [T32Job]:
        T32JobManager.poll_all()
        T32_JOBS

    static fn cancel_job(job_id: text) -> Result<T32Job, text>:
        var jobs = T32_JOBS
        var i = 0
        while i < jobs.len():
            var job = jobs[i]
            if job.job_id == job_id:
                if T32JobManager.is_terminal(job.status):
                    return Err("job {job_id} already in terminal state: {job.status}")
                job.status = "cancelled"
                job.updated_at = rt_time_now_unix_micros()
                job.summary = "cancelled by client"
                # Attempt to interrupt PRACTICE if running:
                # send PRACTICE.CloseAllDialogs() or B:: prefix to break
                jobs[i] = job
                T32_JOBS = jobs
                return Ok(job)
            i = i + 1
        Err("job not found: {job_id}")

    static fn poll_all():
        var jobs = T32_JOBS
        var modified = false
        var i = 0
        val now = rt_time_now_unix_micros()
        while i < jobs.len():
            var job = jobs[i]
            if not T32JobManager.is_terminal(job.status):
                val new_job = T32JobManager.poll_one(job, now)
                if new_job.status != job.status or new_job.updated_at != job.updated_at:
                    jobs[i] = new_job
                    modified = true
            i = i + 1
        if modified:
            T32_JOBS = jobs

    static fn poll_one(job: T32Job, now: i64) -> T32Job:
        # Check timeout first
        val elapsed_ms = (now - job.started_at) / 1000
        if job.timeout_ms > 0 and elapsed_ms > job.timeout_ms:
            job.status = "timed_out"
            job.updated_at = now
            job.error = "timed out after {elapsed_ms}ms (limit: {job.timeout_ms}ms)"
            return job

        # Poll T32 state depending on current status
        val session = t32_find_session(job.session_id)
        if session.?:
            match job.status:
                "running":
                    pass_todo  # dispatch to waiting_practice or waiting_target
                "waiting_practice":
                    val state = t32_poll_practice_state_remote(session!, job)
                    job._last_practice_state = state
                    if state == "0" or state == "idle":
                        job.status = "completed"
                        job.result = t32_capture_area(session!, job._area_name)
                        job.summary = "practice done after {elapsed_ms}ms"
                    elif state == "dialog":
                        job.status = "failed"
                        job.error = "PRACTICE entered dialog state (headless hang)"
                    job.updated_at = now
                "waiting_target":
                    val running = t32_query_state_run(session!)
                    if not running:
                        job.status = "completed"
                        job.summary = "target stopped after {elapsed_ms}ms"
                    job.updated_at = now
                _:
                    pass_do_nothing
        else:
            job.status = "failed"
            job.error = "session {job.session_id} no longer available"
            job.updated_at = now
        job

    static fn cleanup():
        val now = rt_time_now_unix_micros()
        val retention_us = T32_JOB_RETENTION_MS * 1000
        var kept: [T32Job] = []
        for job in T32_JOBS:
            val age = now - job.updated_at
            if not T32JobManager.is_terminal(job.status) or age < retention_us:
                kept = kept + [job]
        T32_JOBS = kept

    static fn count_active() -> i64:
        var n: i64 = 0
        for job in T32_JOBS:
            if not T32JobManager.is_terminal(job.status):
                n = n + 1
        n

    static fn is_terminal(status: text) -> bool:
        (status == "completed" or status == "failed" or
         status == "timed_out" or status == "cancelled")
```

### Storage model

**In-memory array with linear scan.** This matches the existing `BG_TASKS` pattern in `main_lazy_tasks.spl` and is sufficient for the expected scale (a single T32 MCP session rarely has more than a handful of concurrent jobs).

Key policies:

- **Max concurrent jobs:** 16 (configurable). Rejects new jobs with an error when the limit is reached. This prevents runaway job accumulation from misbehaving clients.
- **Retention:** Completed/failed/timed_out/cancelled jobs are kept for 5 minutes (`T32_JOB_RETENTION_MS`) after their last status update, then cleaned up.
- **Cleanup trigger:** `cleanup()` runs whenever `list_jobs()` is called and whenever a new job is created and the array exceeds `T32_MAX_CONCURRENT_JOBS * 2`. This mirrors the existing `bg_task_cleanup()` pattern.
- **No persistence:** Jobs are lost on server restart. This is intentional: T32 session state is also lost on restart, so orphaned jobs have no meaningful resume path.

If dict lookup by job_id becomes a bottleneck (unlikely at scale 16), the array can be replaced with a `Map<text, T32Job>` without changing the external API.

### Integration points

#### t32_cmm_run with background=true

Today `handle_t32_cmm_run` accepts `wait` and `timeout` parameters. Adding `background=true` changes the flow:

```simple
fn handle_t32_cmm_run(id: text, body: text) -> text:
    # ... existing parameter extraction ...
    val background = t32_extract_field(body, "background") == "true"

    if background:
        # Create a job, fire the CMM script, return immediately
        val job = T32JobManager.create_job(
            "t32_cmm_run", session.id, current_core, timeout_ms)?
        job._script_path = script
        job._area_name = MCP_T32_AREA_NAME
        # Fire the script (non-blocking — PRACTICE runs asynchronously)
        t32_run_remote(session, "DO " + script)
        job.status = "waiting_practice"
        job.updated_at = rt_time_now_unix_micros()
        return make_job_handle_response(id, job)

    # ... existing synchronous wait=true/false path unchanged ...
```

#### t32_cmd_run with async mode

Same pattern: when `background=true`, create a job, send the command, and return a job handle. The job manager polls `PRACTICE.STATE()` or checks command completion on subsequent `poll_all()` calls.

For commands classified as `immediate` (e.g., `Register.Set`, `EVAL`), `background=true` is ignored and the tool returns synchronously. This avoids unnecessary job overhead for sub-millisecond operations.

#### t32_job_list, t32_job_get, t32_job_cancel, t32_job_result tools

```simple
fn handle_t32_job_list(id: text, body: text) -> text:
    val jobs = T32JobManager.list_jobs()   # triggers poll_all + cleanup
    # Build JSON array of job summaries (job_id, tool_name, status, elapsed_ms)
    # Omit result/error bodies — use t32_job_get or resource read for those
    make_tool_result(id, format_job_list(jobs))

fn handle_t32_job_get(id: text, body: text) -> text:
    val job_id = t32_extract_field(body, "job_id")
    val job = T32JobManager.get_job(job_id)
    if job.?:
        # Return full job state including result/error
        # Include resource_link to t32:///jobs/<id> for large results
        make_job_detail_response(id, job!)
    else:
        t32_make_error(id, -32602, "Job not found: {job_id}")

fn handle_t32_job_cancel(id: text, body: text) -> text:
    val job_id = t32_extract_field(body, "job_id")
    match T32JobManager.cancel_job(job_id):
        Ok(job): make_tool_result(id, "Job {job_id} cancelled")
        Err(msg): t32_make_error(id, -32602, msg)

fn handle_t32_job_result(id: text, body: text) -> text:
    val job_id = t32_extract_field(body, "job_id")
    val job = T32JobManager.get_job(job_id)
    if job.?:
        val j = job!
        if T32JobManager.is_terminal(j.status):
            make_tool_result(id, j.result)
        else:
            make_tool_result(id, "Job {job_id} still {j.status}")
    else:
        t32_make_error(id, -32602, "Job not found: {job_id}")
```

#### Resources: t32:///jobs/<id>

Add to the existing `t32_handle_resource_read` dispatcher:

```simple
if uri.starts_with("t32:///jobs/"):
    val job_id = uri.substring(12)  # after "t32:///jobs/"
    val job = T32JobManager.get_job(job_id)
    if job.?:
        val j = job!
        val content = format_job_as_resource(j)
        return make_resource_content(id, uri, content)
    return t32_make_error(id, -32002, t32_err_resource_not_found(uri))
```

Also add `t32:///jobs` to `t32_make_resources_list` as a new resource template:

```simple
r4 = r4 + t32_jp("uri", t32_js("t32:///jobs"))
r4 = r4 + "," + t32_jp("name", t32_js("Active jobs"))
r4 = r4 + "," + t32_jp("description", t32_js("List of background T32 jobs"))
```

### Response shape for background launch

When a tool returns a job handle instead of a direct result:

```json
{
  "content": [{"type": "text", "text": "Job j3 started (t32_cmm_run: flash.cmm). Poll with t32_job_get."}],
  "structuredContent": {
    "jobId": "j3",
    "status": "waiting_practice",
    "toolName": "t32_cmm_run",
    "sessionId": "s1",
    "coreId": "core0",
    "elapsed_ms": 12,
    "pollInterval": 2,
    "resourceUri": "t32:///jobs/j3"
  }
}
```

### Polling strategy

#### Server-side (internal poll loop)

The T32 MCP server is single-threaded and stdio-based. There is no background thread to continuously poll. Instead, polling is **request-driven**:

1. **On `t32_job_get` / `t32_job_list` / `t32_job_result`:** Call `T32JobManager.poll_all()` before returning results. This refreshes the status of all non-terminal jobs.

2. **On any tool call for the same session:** Optionally call `poll_all()` to keep job states fresh. This is cheap since it only queries `PRACTICE.STATE()` or `STATE.RUN()` per active job.

3. **PRACTICE.STATE() polling:** Uses the existing `t32_run_remote(session, "EVAL PRACTICE.STATE()")` pattern. The MCP handler already does this with 500ms intervals. For background jobs, the interval is driven by client poll requests, not an internal timer.

#### Client-side poll interval recommendation

Return `pollInterval` (in seconds) in the `structuredContent` of job handle responses:

| Job type | Recommended poll interval |
|----------|--------------------------|
| CMM script (flash/program) | 2-5s |
| CMM script (short) | 1-2s |
| Command run (long) | 1-2s |
| Target run-until-break | 2-5s |
| Trace collection | 5-10s |

The LLM or client can use this to decide when to call `t32_job_get` again.

#### Timeout escalation (foreground -> background)

When `wait=true` and the foreground poll loop reaches `timeout_ms` without completion:

```simple
# In handle_t32_cmm_run, after poll loop times out:
if wait and not practice_done:
    # Instead of returning an error, escalate to background job
    val job = T32JobManager.create_job(
        "t32_cmm_run", session.id, current_core,
        timeout_ms * 10)?  # background gets 10x the foreground timeout
    job.status = "waiting_practice"
    job._script_path = script
    job.summary = "foreground wait timed out after {timeout_ms}ms, continuing in background"
    return make_job_handle_response(id, job)
```

This means a foreground timeout does not kill the operation. The client receives a job handle and can poll for eventual completion. Only `timeout_ms` expiration on the *background* job produces the terminal `timed_out` status.

### Migration path to MCP Tasks (2025-11-25)

When the server upgrades its protocol version, the internal `T32JobManager` maps directly to the Tasks API:

| Internal concept | MCP Tasks equivalent | Change required |
|------------------|---------------------|-----------------|
| `T32Job.job_id` | Task ID (server-generated) | None -- already generated server-side |
| `T32Job.status` | Task state (`running`, `completed`, `failed`, `cancelled`) | Map `waiting_practice`/`waiting_target` to `running` with metadata |
| `T32JobManager.poll_one` | Server-side task progress | Emit `notifications/progress` on state transitions |
| `t32_job_get` | `tasks/get` | Wire protocol handler to `T32JobManager.get_job` |
| `t32_job_list` | `tasks/list` | Wire protocol handler to `T32JobManager.list_jobs` |
| `t32_job_cancel` | `tasks/cancel` | Wire protocol handler to `T32JobManager.cancel_job` |
| `t32_job_result` | Deferred tool result retrieval | Return result via task completion payload |
| `t32:///jobs/<id>` resource | Optional -- keep for large result access | No change needed |

What changes:

- Tool handlers for `t32_cmm_run(background=true)` return a task-backed response instead of a plain tool result with `structuredContent`.
- The server emits `notifications/progress` when `poll_one` detects a state transition, rather than waiting for the client to call `t32_job_get`.
- `t32_job_list`, `t32_job_get`, `t32_job_cancel` can become aliases for `tasks/list`, `tasks/get`, `tasks/cancel` or be deprecated in favor of the protocol-level equivalents.

What stays the same:

- `T32Job` class and all its fields.
- `T32JobManager` and its poll/cleanup logic.
- The PRACTICE.STATE() and STATE.RUN() polling mechanics.
- The resource URI scheme for large results.
- Timeout policy, max concurrent jobs, retention policy.

The migration is a protocol adapter layer on top of the existing job manager, not a redesign.

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

## Implementation Gap Analysis

This section consolidates all identified gaps between the current T32 MCP server implementation and the target state defined by the MCP 2025-06-18 specification, the research recommendations above, and the design documents in this repository. Current protocol compliance is estimated at **52/100** relative to a full SDK-parity implementation.

### Prioritized Gap Table

Priorities: P0 = blocking for production use, P1 = required for acceptable UX, P2 = needed for spec compliance, P3 = nice-to-have / future.
Effort: S = small (1-2 days), M = medium (3-5 days), L = large (1-2 weeks).

#### P0 — Production Blockers

| # | Gap | Current State | Target State | Effort | Depends On |
|---|-----|--------------|--------------|--------|------------|
| G01 | No async/await — all tool calls block | `t32_cmm_run` polls `PRACTICE.STATE()` synchronously; no background execution path | Internal job manager; `background=true` returns job ID immediately; poll via `t32_job_get` | L | — |
| G02 | No connection retry or health check | `session_open` sends a single `PING`; if it fails, connection is reported as `connected=false` with no retry, no backoff, no reconnect | Configurable retry with exponential backoff (3 attempts default); periodic health PING; auto-reconnect on transient failure | M | — |
| G03 | Session state lost on server restart | All session, field, and history state is in module-level `var` lists (`MCP_T32_SESSIONS`, `MCP_T32_FIELD_STATE`, `MCP_T32_FIELD_VALUES`, `MCP_T32_HISTORY`); process exit discards everything | Persist session manifest and field cache to a file or SDN store; restore on startup via `session_resume` | M | — |
| G04 | Window catalog SDN parse errors silently fail | `t32_get_window_catalog()` reads `config/t32/catalogs/windows.sdn`; on any read failure or empty parse result, falls back to hardcoded entries without reporting the error | Log SDN parse failure via MCP Logging API (G09); return `"catalog_source": "fallback"` in tool results so the user knows the catalog is degraded | S | G09 |

#### P1 — UX-Critical

| # | Gap | Current State | Target State | Effort | Depends On |
|---|-----|--------------|--------------|--------|------------|
| G05 | No window snapshots or diff-aware responses | `t32_window_capture` always returns full window text; no snapshot store, no hash comparison, no diff | Per-session snapshot store with `last_content`, `last_hash`; `mode=summary\|diff\|full`; structured row diff for label/value windows | L | — |
| G06 | No Streamable HTTP Transport | Server is stdio-only (`t32_read_stdin_message` / `t32_write_stdout_message`) | Add HTTP/SSE transport option for remote and multi-client scenarios per MCP 2025-06-18 transport spec | L | — |
| G07 | No Progress Notifications | Long-running `t32_cmm_run` and `t32_cmd_run` calls provide no incremental feedback | Emit `notifications/progress` with `progressToken`, percentage, and message during CMM polling and flash operations | M | G01 |
| G08 | No MCP Logging API | Server writes diagnostics to stderr via `t32_startup_diag`; no structured log messages to client | Implement `logging/setLevel` handler; emit `notifications/message` at configured severity; route `t32_startup_diag` and SDN parse warnings through it | M | — |
| G09 | CMM validation exists in LSP but NOT exposed via T32 MCP | `cmm_validate_cli` is implemented in `t32_lsp_mcp/tools.spl` with 7 checks (GUI keywords, DIALOG patterns, INKEY/ENTER/PAUSE, unbounded WAIT, SCREEN.WAIT, ENDDO, parse errors); the T32 MCP server has blocking pattern detection in `session_tools.spl` but only as a gate on `t32_cmd_run` — no standalone validation tool | Add `t32_cmm_validate` tool to the T32 MCP server that exposes the same checks; optionally call the LSP MCP as a subprocess or share the validation module | M | — |

#### P2 — Spec Compliance

| # | Gap | Current State | Target State | Effort | Depends On |
|---|-----|--------------|--------------|--------|------------|
| G10 | Linear field state lookup O(N) | `t32_field_state_get` iterates parallel lists `MCP_T32_FIELD_STATE` / `MCP_T32_FIELD_VALUES` with a `for` loop; every get/set is O(N) | Replace with `Dict<text, text>` keyed by `"session_id:field_key"`; O(1) amortized lookup | S | — |
| G11 | Tool Annotations only partial | `readOnlyHint`, `destructiveHint`, `idempotentHint`, `openWorldHint` are emitted but with static values per tool; no `title` or `description` annotations on individual tools beyond the top-level description | Add `title` field; set `openWorldHint` accurately per tool (e.g., `t32_cmd_run` is open-world, `t32_sessions_list` is not) | S | — |
| G12 | Structured Output (`outputSchema`) not used | Tool schemas define `inputSchema` only; no `outputSchema` declared | Add `outputSchema` for key tools (`t32_session_open`, `t32_eval`, `t32_field_get`, `t32_window_capture`, `t32_job_get`) so clients can validate structured responses | M | — |
| G13 | No Pagination | `t32_window_list`, `t32_history_tail`, `t32_cmm_commands`, and resource reads return unbounded results | Implement cursor-based pagination on list tools and resource reads per MCP pagination spec; default page size 50 | M | — |
| G14 | No Resource Subscriptions | Resources (`t32:///sessions`, `t32:///windows`, `t32:///history`) are read-only pull; no change notifications | Implement `resources/subscribe` and `resources/unsubscribe`; emit `notifications/resources/updated` when session state or window content changes | M | G05 |
| G15 | No transaction support for multi-step operations | Each tool call is independent; a flash-then-verify or set-breakpoint-then-run sequence can be interrupted or partially applied | Add `t32_transaction_begin` / `t32_transaction_commit` / `t32_transaction_rollback` tool set; queue commands and execute atomically | L | G01 |

#### P3 — Future / Nice-to-Have

| # | Gap | Current State | Target State | Effort | Depends On |
|---|-----|--------------|--------------|--------|------------|
| G16 | No job queue or background task scheduling | No concept of queued work; everything runs immediately or blocks | Priority job queue with configurable concurrency limit (default 1 per session); job retention with TTL | L | G01 |
| G17 | T32 MCP async not integrated into LSP/DAP roadmap | T32 MCP and T32 LSP MCP are separate servers with no shared session or event model; DAP integration is not started | Unified session layer shared between MCP, LSP, and future DAP; event bus for cross-protocol notifications | L | G01, G05 |
| G18 | Active deployment uses `main.spl`, not `main_lazy.spl` | `.mcp.json` references `bin/t32_mcp_server` which compiles from `main.spl`; `main_lazy.spl` does not exist despite design doc references | Either create a lazy-init variant or update design docs to reflect that `main.spl` is the canonical entry point | S | — |

### Dependency Graph

```
G01 (Job Manager)
 ├── G07 (Progress Notifications)
 ├── G15 (Transactions)
 ├── G16 (Job Queue)
 └── G17 (LSP/DAP Integration)

G05 (Window Snapshots)
 ├── G14 (Resource Subscriptions)
 └── G17 (LSP/DAP Integration)

G08 (Logging API)
 └── G04 (SDN Parse Error Reporting)

All others are independent or have only soft ordering preferences.
```

### Risk Assessment

| Risk | Severity | Likelihood | Mitigation |
|------|----------|------------|------------|
| **Job manager introduces race conditions** — module-level mutable state is already fragile; adding background jobs to the single-threaded event loop requires careful interleaving | High | Medium | Keep job execution cooperative (poll-based, not threaded) in phase 1; add mutex/channel only when Simple's async runtime is proven stable for MCP use |
| **SDN catalog silent failures mask real config bugs** — users may debug wrong window metadata for hours without realizing the catalog fell back to hardcoded data | Medium | High | G04 is low effort; prioritize it even before G01. Add `"catalog_source"` field to every catalog-dependent response |
| **Streaming HTTP transport doubles the protocol surface** — maintaining both stdio and HTTP increases test burden and bug surface | Medium | Medium | Implement HTTP transport behind a feature flag; keep stdio as the default and only supported mode in phase 1 |
| **Session persistence creates stale state** — persisted sessions may reference T32 instances that have since disconnected or changed core configuration | Medium | High | Validate persisted sessions with a PING on restore; mark unresponsive sessions as `stale` rather than `connected`; auto-expire after configurable TTL |
| **Linear field lookup is a correctness risk, not just perf** — if `MCP_T32_FIELD_STATE` and `MCP_T32_FIELD_VALUES` lists get out of sync (e.g., partial append failure), lookups silently return wrong values | High | Low | G10 is S-effort and eliminates the structural risk; prioritize it in the first sprint |
| **CMM validation gap between LSP and MCP** — the LSP server has 7 validation checks; the MCP server has a simpler blocking pattern detector in `session_tools.spl`. Users of T32 MCP alone get weaker safety guarantees | Medium | High | G09 unifies the validation; share the module or call the LSP server as a subprocess. Short-term: document that `t32-lsp-mcp` provides stronger validation |
| **No pagination risks token budget blowout** — `t32_cmm_commands` returns 120+ commands; `t32_history_tail` is unbounded; Claude Code warns at 10K tokens and caps at 25K | High | High | G13 is M-effort but high impact. Interim: add hard caps to list tools (e.g., max 50 entries) even before implementing cursor pagination |

### Recommended Execution Order

**Sprint 1 (P0 + quick P1/P2 wins):**
G10 (Dict-based field lookup, S), G04 (SDN error reporting, S), G18 (main_lazy doc fix, S), G11 (annotation accuracy, S), G08 (Logging API, M)

**Sprint 2 (Core async + UX):**
G01 (Job manager, L), G02 (Connection retry, M), G07 (Progress notifications, M)

**Sprint 3 (Spec compliance):**
G03 (Session persistence, M), G05 (Window snapshots, L), G09 (CMM validate in MCP, M), G12 (outputSchema, M)

**Sprint 4 (Full compliance):**
G13 (Pagination, M), G14 (Resource subscriptions, M), G06 (HTTP transport, L)

**Sprint 5 (Future):**
G15 (Transactions, L), G16 (Job queue, L), G17 (LSP/DAP integration, L)

### Design Document Contradictions

Three contradictions were found between design documents and the actual implementation:

1. **Active deployment is `main.spl`, not `main_lazy.spl`.** The `.mcp.json` config points to `bin/t32_mcp_server` which builds from `main.spl`. No `main_lazy.spl` file exists in the T32 MCP directory. Design documents referencing a lazy-init entry point are outdated.

2. **T32 MCP async is not integrated into the LSP/DAP roadmap.** The T32 MCP server and T32 LSP MCP server are fully independent processes with separate protocol handling, separate JSON helpers (prefixed `t32_` vs `lsp_`), and no shared session state. The phased roadmap in this document proposes a job manager, but it does not address how jobs, sessions, or events would flow between MCP and a future DAP server.

3. **Symbol/type resources are absent, not stubs.** The resource list exposes only `t32:///sessions`, `t32:///windows`, and `t32:///history`. There are no `t32:///symbols` or `t32:///types` resources, stub or otherwise. Any design documents referencing symbol/type resources via MCP describe future intent, not current state.

## Window Snapshot Implementation Design

This section details the concrete implementation design for the window snapshot/diff system outlined in the "Window and Status UX for Claude" section above. The design covers the snapshot store, layered diff algorithms, window type classification, MCP response shaping, and watched-window integration.

### Snapshot Store

The snapshot store is a module-level in-memory cache keyed by `(session_id, core_id, window_key)`. Each entry holds the last captured content, its structural parse (if applicable), and a hash for fast change detection.

```simple
class T32WindowSnapshot:
    window_key: text
    title: text
    session_id: text
    core_id: text
    captured_at: i64              # Unix timestamp ms
    content_hash: text            # djb2-style string hash
    raw_content: text             # Full captured text
    structured_rows: [Dict<text, text>]  # Parsed rows if parseable, empty otherwise
    diff_strategy: text           # "structured_row" | "table" | "text"
    row_count: i64                # Number of parsed rows (0 = unparsed)

class T32SnapshotStore:
    snapshots: Dict<text, T32WindowSnapshot>  # key = "{session_id}/{core_id}/{window_key}"
    max_entries: i64              # Eviction cap (default: 200)
    ttl_ms: i64                   # Time-to-live per entry (default: 300_000 = 5 min)

    fn store_key(session_id: text, core_id: text, window_key: text) -> text:
        "{session_id}/{core_id}/{window_key}"

    fn get(session_id: text, core_id: text, window_key: text) -> Option<T32WindowSnapshot>:
        val key = self.store_key(session_id, core_id, window_key)
        val snap = self.snapshots.get(key)
        match snap:
            nil: nil
            Some(s):
                val now = rt_time_ms()
                if now - s.captured_at > self.ttl_ms:
                    # Expired — treat as miss
                    self.snapshots.remove(key)
                    nil
                else:
                    Some(s)

    me put(snapshot: T32WindowSnapshot):
        val key = self.store_key(snapshot.session_id, snapshot.core_id, snapshot.window_key)
        # Evict oldest if at capacity
        if self.snapshots.len() >= self.max_entries and not self.snapshots.has(key):
            self.evict_oldest()
        self.snapshots.set(key, snapshot)

    me evict_oldest():
        var oldest_key = ""
        var oldest_time: i64 = i64.max
        for (k, v) in self.snapshots:
            if v.captured_at < oldest_time:
                oldest_time = v.captured_at
                oldest_key = k
        if oldest_key != "":
            self.snapshots.remove(oldest_key)

    me clear_session(session_id: text):
        var to_remove: [text] = []
        for (k, _v) in self.snapshots:
            if k.starts_with("{session_id}/"):
                to_remove.push(k)
        for k in to_remove:
            self.snapshots.remove(k)
```

Hash computation uses the same approach already proven in `mcp_t32_state_diff_spec.spl`, upgraded to djb2 seeding for better distribution:

```simple
fn snapshot_hash(content: text) -> text:
    # djb2-style hash — fast, sufficient for change detection (not cryptographic)
    var hash: i64 = 5381
    var i = 0
    while i < content.len():
        hash = hash * 33 + content[i].bytes()[0]
        i = i + 1
    str(hash)
```

Module-level state adds one global store instance alongside existing session state:

```simple
# Added to main.spl alongside MCP_T32_SESSIONS, MCP_T32_HISTORY, etc.
var MCP_T32_SNAPSHOT_STORE = T32SnapshotStore(
    snapshots: {},
    max_entries: 200,
    ttl_ms: 300_000
)
```

### Diff Algorithm Layers

The diff system uses three layers, selected by the window's diff strategy classification. Each layer returns a `T32WindowDiff` structure:

```simple
class T32DiffEntry:
    kind: text        # "changed" | "added" | "removed"
    label: text       # Row label, cell address, or line number
    field: text       # Field name within the row (or "" for line-level)
    old_value: text
    new_value: text

class T32WindowDiff:
    strategy_used: text         # "structured_row" | "table" | "text" | "full"
    change_count: i64
    entries: [T32DiffEntry]
    confidence: f64             # 0.0-1.0 — how trustworthy the diff is
    truncated: bool             # True if entries were capped for token budget
```

#### Layer 1: Structured Row Diff

Used for windows whose output parses into `label -> value` pairs: register windows, system status, peripheral views, flash status, variable watches. These windows have a natural primary key per row (the register name, peripheral name, variable name).

```simple
fn diff_structured_rows(
    old_rows: [Dict<text, text>],
    new_rows: [Dict<text, text>],
    key_field: text                   # e.g. "name" for registers
) -> T32WindowDiff:
    var entries: [T32DiffEntry] = []

    # Index old rows by key
    var old_index: Dict<text, Dict<text, text>> = {}
    for row in old_rows:
        val k = row.get(key_field) ?? ""
        if k != "":
            old_index.set(k, row)

    # Compare new rows against old
    for row in new_rows:
        val k = row.get(key_field) ?? ""
        if k == "":
            continue
        val old_row = old_index.get(k)
        match old_row:
            nil:
                # Added row
                entries.push(T32DiffEntry(
                    kind: "added", label: k, field: "",
                    old_value: "", new_value: row_to_text(row)
                ))
            Some(prev):
                # Compare each field
                for (field, new_val) in row:
                    if field == key_field:
                        continue
                    val old_val = prev.get(field) ?? ""
                    if old_val != new_val:
                        entries.push(T32DiffEntry(
                            kind: "changed", label: k, field: field,
                            old_value: old_val, new_value: new_val
                        ))
                old_index.remove(k)

    # Remaining old entries are removed rows
    for (k, prev) in old_index:
        entries.push(T32DiffEntry(
            kind: "removed", label: k, field: "",
            old_value: row_to_text(prev), new_value: ""
        ))

    T32WindowDiff(
        strategy_used: "structured_row",
        change_count: entries.len(),
        entries: entries,
        confidence: 0.95,
        truncated: false
    )
```

Example output for a register window diff:

```
changed  PC     value  0x08001234 -> 0x08001238
changed  LR     value  0x08000100 -> 0x08000200
```

#### Layer 2: Table Diff

Used for grid-shaped windows: memory dumps (`address | hex_bytes | ascii`), stack frames (`frame_id | address | function | file_line`), breakpoint lists, coverage tables, task lists, trace records. Rows are keyed by position-dependent identifiers (address, frame id, line number).

```simple
fn diff_table_rows(
    old_rows: [Dict<text, text>],
    new_rows: [Dict<text, text>],
    key_field: text                    # e.g. "address" for memory, "frame_id" for stack
) -> T32WindowDiff:
    var entries: [T32DiffEntry] = []

    # Build old index
    var old_index: Dict<text, Dict<text, text>> = {}
    for row in old_rows:
        val k = row.get(key_field) ?? ""
        if k != "":
            old_index.set(k, row)

    # Diff by key
    for row in new_rows:
        val k = row.get(key_field) ?? ""
        if k == "":
            continue
        val old_row = old_index.get(k)
        match old_row:
            nil:
                entries.push(T32DiffEntry(
                    kind: "added", label: k, field: "",
                    old_value: "", new_value: row_to_text(row)
                ))
            Some(prev):
                for (field, new_val) in row:
                    if field == key_field:
                        continue
                    val old_val = prev.get(field) ?? ""
                    if old_val != new_val:
                        entries.push(T32DiffEntry(
                            kind: "changed", label: k, field: field,
                            old_value: old_val, new_value: new_val
                        ))
                old_index.remove(k)

    for (k, prev) in old_index:
        entries.push(T32DiffEntry(
            kind: "removed", label: k, field: "",
            old_value: row_to_text(prev), new_value: ""
        ))

    # Table diffs can be noisy when the entire view shifts (e.g., scrolling memory dump)
    # Lower confidence when >60% of rows changed
    val total_rows = max(old_rows.len(), new_rows.len())
    val changed_ratio = if total_rows > 0: entries.len().to_f64() / total_rows.to_f64() else: 0.0
    val confidence = if changed_ratio > 0.6: 0.4 else: 0.85

    T32WindowDiff(
        strategy_used: "table",
        change_count: entries.len(),
        entries: entries,
        confidence: confidence,
        truncated: false
    )
```

Example output for a memory dump diff:

```
changed  D:0x20000004:  hex_bytes  00 00 00 00 -> 2A 00 00 00
added    D:0x20000010:             48 65 6C 6C  Hell
```

#### Layer 3: Text Diff (Fallback)

Used for windows that either do not parse structurally or whose parse failed. Performs line-level comparison with minimal surrounding context. Primary targets: source listings (where line content changes matter more than positional keys), semihosting AREA output, and any window where structured parsing returned zero rows.

```simple
fn diff_text_lines(old_content: text, new_content: text) -> T32WindowDiff:
    val old_lines = old_content.split("\n")
    val new_lines = new_content.split("\n")
    var entries: [T32DiffEntry] = []

    # Simple LCS-based or line-by-line comparison
    # For token budget, limit context to changed lines + 1 surrounding line
    val max_old = old_lines.len()
    val max_new = new_lines.len()
    var oi = 0
    var ni = 0
    while oi < max_old and ni < max_new:
        if old_lines[oi] == new_lines[ni]:
            oi = oi + 1
            ni = ni + 1
            continue
        # Lines differ
        entries.push(T32DiffEntry(
            kind: "changed",
            label: "L{ni + 1}",
            field: "",
            old_value: old_lines[oi],
            new_value: new_lines[ni]
        ))
        oi = oi + 1
        ni = ni + 1

    # Handle trailing additions/removals
    while ni < max_new:
        entries.push(T32DiffEntry(
            kind: "added", label: "L{ni + 1}", field: "",
            old_value: "", new_value: new_lines[ni]
        ))
        ni = ni + 1
    while oi < max_old:
        entries.push(T32DiffEntry(
            kind: "removed", label: "L{oi + 1}", field: "",
            old_value: old_lines[oi], new_value: ""
        ))
        oi = oi + 1

    val total_lines = max(max_old, max_new)
    val changed_ratio = if total_lines > 0: entries.len().to_f64() / total_lines.to_f64() else: 0.0
    val confidence = if changed_ratio > 0.5: 0.3 else: 0.7

    T32WindowDiff(
        strategy_used: "text",
        change_count: entries.len(),
        entries: entries,
        confidence: confidence,
        truncated: false
    )
```

#### Confidence Scoring and Full-Content Fallback

When confidence drops below a threshold, the server abandons the diff and returns full content instead. This prevents confusing diffs when the window layout changed dramatically (e.g., switching from one symbol's register view to another, scrolling a memory dump by a large offset, or a source listing jumping to a different file).

```simple
val DIFF_CONFIDENCE_THRESHOLD: f64 = 0.4

fn should_use_full_content(diff: T32WindowDiff) -> bool:
    # Fall back to full when:
    # 1. Confidence is below threshold
    # 2. Change count exceeds what fits comfortably in token budget
    # 3. The diff itself would be larger than the full content
    if diff.confidence < DIFF_CONFIDENCE_THRESHOLD:
        return true
    if diff.change_count > 50:
        return true
    false
```

### Window Type Classification

The window catalog SDN already defines `kind: built_in` for all entries. The diff strategy extends this by mapping each `window_key` to its diff algorithm layer. This mapping is static and derived from the known parser structure for each window.

| Window Key | Parser Shape | Key Field | Diff Strategy |
|---|---|---|---|
| `register_view` | `name=value` pairs | `name` | `structured_row` |
| `riscv_csr_view` | `name=value` pairs | `name` | `structured_row` |
| `per_view` | `name\|address\|value\|bits` | `name` | `structured_row` |
| `var_local` | `name\|type\|value` | `name` | `structured_row` |
| `var_watch` | `name\|type\|value` | `name` | `structured_row` |
| `system_status` | `name=value` pairs | `name` | `structured_row` |
| `flash_status` | tabular status | `name` | `structured_row` |
| `memory_dump` | `address\|hex_bytes\|ascii` | `address` | `table` |
| `stack_frame` | `frame_id\|address\|function\|file_line` | `frame_id` | `table` |
| `break_list` | `enabled\|address\|symbol\|type` | `address` | `table` |
| `coverage_list` | `function\|percent\|hits` | `function` | `table` |
| `task_list` | tabular rows | `task_id` | `table` |
| `trace_list` | tabular rows | row index | `table` |
| `nexus_trace` | tabular rows | row index | `table` |
| `mmu_list` | `virt_addr\|phys_addr\|size\|perms` | `virt_addr` | `table` |
| `perf_list` | `module\|time\|calls\|percent` | `module` | `table` |
| `symbol_browse` | `name\|address\|size\|type` | `name` | `table` |
| `source_list` | `line_number\|address\|source` | `line_number` | `text` |
| `data_list` | `address\|instruction\|symbol` | `address` | `table` |
| `semihost_area` | free-form text | n/a | `text` |

Implementation as a lookup function:

```simple
fn window_diff_strategy(window_key: text) -> (text, text):
    # Returns (strategy, key_field)
    match window_key:
        "register_view": ("structured_row", "name")
        "riscv_csr_view": ("structured_row", "name")
        "per_view": ("structured_row", "name")
        "var_local": ("structured_row", "name")
        "var_watch": ("structured_row", "name")
        "system_status": ("structured_row", "name")
        "flash_status": ("structured_row", "name")
        "memory_dump": ("table", "address")
        "stack_frame": ("table", "frame_id")
        "break_list": ("table", "address")
        "coverage_list": ("table", "function")
        "task_list": ("table", "task_id")
        "trace_list": ("table", "index")
        "nexus_trace": ("table", "index")
        "mmu_list": ("table", "virt_addr")
        "perf_list": ("table", "module")
        "symbol_browse": ("table", "name")
        "data_list": ("table", "address")
        "source_list": ("text", "")
        "semihost_area": ("text", "")
        _: ("text", "")                     # Unknown windows fall back to text diff
```

### MCP Response Shaping

The `t32_window_capture` tool gains a `mode` parameter that controls response verbosity. The three modes address distinct use cases in the Claude Code workflow.

#### Mode Definitions

**`mode=summary`** (default after first capture)

Returns a one-line status. Ideal for post-command status checks where the LLM only needs to know whether something changed.

```json
{
    "window": "register_view",
    "title": "CPU Registers",
    "changed": true,
    "change_count": 3,
    "content_preview": "PC: 0x08001234->0x08001238, LR: 0x100->0x200, +1 more",
    "full_resource_uri": "t32://windows/t32_1/core0/register_view"
}
```

Estimated token cost: 50-100 tokens.

**`mode=diff`** (explicit request or auto for watched windows)

Returns the structured diff payload. Used when the LLM needs to reason about specific value changes.

```json
{
    "window": "register_view",
    "title": "CPU Registers",
    "changed": true,
    "change_count": 2,
    "diff_strategy": "structured_row",
    "diff_confidence": 0.95,
    "window_diff": [
        {"kind": "changed", "label": "PC", "field": "value",
         "old": "0x08001234", "new": "0x08001238"},
        {"kind": "changed", "label": "LR", "field": "value",
         "old": "0x08000100", "new": "0x08000200"}
    ],
    "full_resource_uri": "t32://windows/t32_1/core0/register_view"
}
```

Estimated token cost: 200-2,000 tokens depending on change count. The server enforces a hard cap: if the serialized `window_diff` array exceeds 8,000 tokens (estimated at ~4 chars/token), the response automatically downgrades to summary mode and sets `"diff_truncated": true`.

**`mode=full`** (explicit request or first capture)

Returns the complete raw content inline. Used for initial inspection or when the LLM needs the full picture.

```json
{
    "window": "register_view",
    "title": "CPU Registers",
    "changed": true,
    "change_count": 2,
    "content": "R0=0x00000000  R1=0x20001000  R2=0x08001234 ...",
    "structured_rows": [
        {"name": "R0", "value": "0x00000000"},
        {"name": "R1", "value": "0x20001000"}
    ],
    "full_resource_uri": "t32://windows/t32_1/core0/register_view"
}
```

Estimated token cost: 500-10,000 tokens. If full content exceeds 10,000 tokens, the server truncates the inline `content` field, sets `"content_truncated": true`, and the LLM can use the `full_resource_uri` resource to read the remainder.

#### Resource URI Scheme

Full window content is always available through MCP resources at:

```
t32://windows/<session_id>/<core_id>/<window_key>
```

These resources are served from the snapshot store, so they reflect the most recent capture without requiring a new WinPrint round-trip. The resource read handler:

```simple
fn handle_resource_read(uri: text) -> text:
    # Parse "t32://windows/<session>/<core>/<window>"
    val parts = uri.replace("t32://windows/", "").split("/")
    if parts.len() < 3:
        return resource_error("invalid URI")
    val session_id = parts[0]
    val core_id = parts[1]
    val window_key = parts[2]
    val snap = MCP_T32_SNAPSHOT_STORE.get(session_id, core_id, window_key)
    match snap:
        nil: resource_error("no snapshot available — capture the window first")
        Some(s): s.raw_content
```

#### Token Budget Awareness

The server tracks estimated output size at serialization time:

```simple
val TOKEN_WARNING_THRESHOLD: i64 = 10_000    # Claude Code warns above this
val TOKEN_HARD_CAP: i64 = 25_000             # Claude Code default MAX_MCP_OUTPUT_TOKENS
val CHARS_PER_TOKEN: i64 = 4                 # Conservative estimate

fn estimate_tokens(content: text) -> i64:
    content.len() / CHARS_PER_TOKEN

fn apply_token_budget(response: text, mode: text) -> text:
    val est = estimate_tokens(response)
    if est <= TOKEN_WARNING_THRESHOLD:
        return response
    if mode == "full" and est > TOKEN_HARD_CAP:
        # Truncate content field, keep metadata
        return truncate_content_field(response, TOKEN_HARD_CAP * CHARS_PER_TOKEN)
    if mode == "diff" and est > TOKEN_WARNING_THRESHOLD:
        # Downgrade to summary
        return rebuild_as_summary(response)
    response
```

### Capture-and-Diff Pipeline

The core capture flow integrates the snapshot store and diff layers into the existing `handle_t32_window_capture` handler:

```simple
fn capture_with_diff(
    session: McpT32Session,
    window_key: text,
    core_id: text,
    mode: text                        # "summary" | "diff" | "full" | "auto"
) -> text:
    # 1. Capture fresh content via existing WinPrint/PRinTer.FILE path
    val raw_content = t32_capture_window_text(session.client, window_key)?
    val new_hash = snapshot_hash(raw_content)

    # 2. Look up previous snapshot
    val prev = MCP_T32_SNAPSHOT_STORE.get(session.id, core_id, window_key)

    # 3. Parse structured rows using the appropriate parser
    val (strategy, key_field) = window_diff_strategy(window_key)
    val new_rows = parse_window_content(window_key, raw_content)

    # 4. Store new snapshot
    val new_snap = T32WindowSnapshot(
        window_key: window_key,
        title: lookup_window_title(window_key),
        session_id: session.id,
        core_id: core_id,
        captured_at: rt_time_ms(),
        content_hash: new_hash,
        raw_content: raw_content,
        structured_rows: new_rows,
        diff_strategy: strategy,
        row_count: new_rows.len()
    )
    MCP_T32_SNAPSHOT_STORE.put(new_snap)

    # 5. Determine effective mode
    val effective_mode = match mode:
        "auto":
            match prev:
                nil: "full"               # First capture — show everything
                Some(p):
                    if p.content_hash == new_hash:
                        "summary"         # Unchanged — minimal response
                    else:
                        "diff"            # Changed — show what changed
        _: mode

    # 6. Compute diff if needed
    match prev:
        nil:
            return format_full_response(new_snap)
        Some(p):
            if p.content_hash == new_hash:
                return format_unchanged_response(new_snap)

            val diff = match strategy:
                "structured_row":
                    diff_structured_rows(p.structured_rows, new_rows, key_field)
                "table":
                    diff_table_rows(p.structured_rows, new_rows, key_field)
                _:
                    diff_text_lines(p.raw_content, raw_content)

            # 7. Check confidence — fall back to full if too low
            if should_use_full_content(diff):
                return format_full_response(new_snap)

            # 8. Format based on effective mode
            match effective_mode:
                "summary": format_summary_response(new_snap, diff)
                "diff": format_diff_response(new_snap, diff)
                "full": format_full_response(new_snap)
                _: format_diff_response(new_snap, diff)
```

### Integration with Watched Windows

Watched windows allow the server to automatically refresh and diff a configurable set of windows after certain commands execute, reporting only those that changed. This eliminates the need for the LLM to issue separate capture calls after every step/continue/register-write operation.

#### Watch List State

```simple
class T32WatchEntry:
    window_key: text
    mode: text                    # "summary" | "diff" — full is too expensive for auto-refresh
    enabled: bool

# Module-level state
var MCP_T32_WATCH_LIST: [T32WatchEntry] = []
```

#### Watch Configuration Tool

```simple
# New tool: t32_window_watch
# Parameters:
#   action: "add" | "remove" | "list" | "clear"
#   window: text (window_key)
#   mode: "summary" | "diff" (default: "summary")

fn handle_t32_window_watch(id: text, body: text) -> text:
    val action = t32_extract_field(body, "action")
    val window_key = t32_extract_field(body, "window")
    val mode = t32_extract_field(body, "mode")
    val effective_mode = if mode == "": "summary" else: mode

    match action:
        "add":
            MCP_T32_WATCH_LIST.push(T32WatchEntry(
                window_key: window_key,
                mode: effective_mode,
                enabled: true
            ))
            t32_make_tool_result(id, "{\"status\": \"watching\", \"window\": \"{window_key}\"}")
        "remove":
            MCP_T32_WATCH_LIST = MCP_T32_WATCH_LIST.filter(\e: e.window_key != window_key)
            t32_make_tool_result(id, "{\"status\": \"removed\", \"window\": \"{window_key}\"}")
        "list":
            val entries = MCP_T32_WATCH_LIST.map(\e: "{\"window\": \"{e.window_key}\", \"mode\": \"{e.mode}\"}")
            t32_make_tool_result(id, "{\"watched\": [{entries.join(\", \")}]}")
        "clear":
            MCP_T32_WATCH_LIST = []
            t32_make_tool_result(id, "{\"status\": \"cleared\"}")
        _:
            t32_make_tool_error(id, -32602, "action must be add|remove|list|clear")
```

#### Auto-Refresh on Command Execution

After any command that may change target state (`t32_cmd_run`, `t32_cmm_run`, step/continue operations), the server silently refreshes all watched windows and appends a `watched_windows` section to the tool response. Only changed windows appear in the output.

```simple
fn refresh_watched_windows(session: McpT32Session, core_id: text) -> [text]:
    # Returns JSON fragments for changed windows only
    var results: [text] = []
    for entry in MCP_T32_WATCH_LIST:
        if not entry.enabled:
            continue
        val response = capture_with_diff(session, entry.window_key, core_id, entry.mode)
        # Only include in output if changed
        if response_indicates_change(response):
            results.push(response)
    results

fn append_watch_results(tool_response: text, watch_results: [text]) -> text:
    if watch_results.len() == 0:
        return tool_response
    # Inject watched_windows array into the structured response
    val watch_json = "[" + watch_results.join(", ") + "]"
    # Append before closing brace of the tool result
    tool_response.replace_last("}", ", \"watched_windows\": {watch_json}}")
```

Example combined response after a step command with `register_view` and `break_list` watched:

```json
{
    "command": "Step",
    "status": "ok",
    "watched_windows": [
        {
            "window": "register_view",
            "title": "CPU Registers",
            "changed": true,
            "change_count": 1,
            "content_preview": "PC: 0x08001234->0x08001238"
        }
    ]
}
```

In this example, `break_list` is also watched but was unchanged, so it is omitted entirely. This keeps the response compact.

#### Watch Budget Limits

To prevent watched windows from bloating responses:

- Maximum 5 watched windows per session.
- Watch mode is limited to `summary` or `diff`, never `full`.
- Total watched-window output is capped at 3,000 estimated tokens. If exceeded, later entries degrade to summary mode.
- Watched windows whose last capture is less than 500ms old are skipped (debounce).

```simple
val MAX_WATCHED_WINDOWS: i64 = 5
val WATCH_TOKEN_BUDGET: i64 = 3_000
val WATCH_DEBOUNCE_MS: i64 = 500
```

### Relationship to Existing Code

This design builds directly on existing infrastructure:

- **Capture path**: unchanged -- `WinPrint.*` primary, `PRinTer.FILE` fallback, as implemented in `window_tools.spl`
- **Parsers**: the 16 window parsers in `t32_window_capture.spl` and tested in `t32_cli_window_parsers_spec.spl` become the structured row producers for diff layers 1 and 2
- **Hash function**: extends the `simple_hash` from `mcp_t32_state_diff_spec.spl` to use djb2 seeding for better distribution
- **State diff**: the `TestStepState.window_snapshots` pattern of `"key|hash"` is the same conceptual model, now backed by a proper store with TTL and eviction
- **Window catalog**: `config/t32/catalogs/windows.sdn` already defines all window keys and their capture commands; the diff strategy table adds one new mapping dimension without changing the catalog format
- **Module state**: the snapshot store sits alongside the existing `MCP_T32_SESSIONS`, `MCP_T32_HISTORY`, and `MCP_T32_AREA_*` module globals in `main.spl`

No changes to the SDN catalog format or the existing tool schema are required. The only additions are the `mode` parameter on `t32_window_capture`, the new `t32_window_watch` tool, and the snapshot store module state.

## CMM Validator MCP Exposure

### Why expose cmm_validate_cli in T32 MCP (not just LSP)

The `cmm_validate_cli` tool currently lives only in the T32 LSP MCP server (`t32_lsp_mcp/tools.spl`). It checks 7 quality dimensions: GUI keyword absence, `SCREEN.OFF` presence, AREA channel setup, `ON ERROR` handler, metadata headers, `ENDDO` return values, and parse validity. That is useful for editor-time feedback, but the more consequential consumer is the T32 MCP server itself, which is where scripts are actually executed headlessly.

Reasons to expose validation in T32 MCP:

1. **Pre-flight check at execution time.** The T32 MCP `t32_cmm_run` handler already runs `t32_check_blocking()` before executing scripts. That function detects BLOCK/WARN/INFO patterns but does not assess CLI conversion quality (missing AREA setup, missing error handlers, missing parameterization). Exposing the validator gives the LLM a single tool call to get both blocking detection and quality assessment before deciding whether to run or rewrite.

2. **Validator-assisted conversion workflow.** The research recommendation is validator-assisted manual conversion, not automatic rewriting. For that workflow to function inside an MCP session, the LLM needs the validator available in the same server where it runs commands. Switching to a separate LSP MCP server mid-workflow breaks context.

3. **Report-driven decision making.** The current `t32_check_blocking()` returns flat warning strings with `BLOCK:`/`WARN:`/`INFO:` prefixes. A structured validation report with severity classes, line numbers, and suggested rewrites gives the LLM enough information to propose targeted edits rather than guessing.

4. **Consistency with blocking detection.** The T32 MCP already has blocking pattern infrastructure (`t32_check_blocking`, `t32_has_blocking`, `t32_blocking_result`, `t32_scan_cmm_file`). Adding a validator tool that reuses this infrastructure plus the LSP-side quality checks creates a single authoritative assessment.

### Proposed MCP tool schema

```
t32_cmm_validate(source: text, mode: text)
```

Parameters:

- `source` (required): CMM script content or file path. If the value contains no newlines and ends with `.cmm`, read the file first.
- `mode` (required): one of `check`, `report`, or `suggest`.

#### mode=check: blocking pattern detection only

Returns the same information as the current `t32_check_blocking()` but in structured form:

```json
{
  "classification": "safe | needs_manual_rewrite | unsafe_for_headless",
  "block_count": 2,
  "warn_count": 1,
  "info_count": 1,
  "patterns": [
    {"severity": "block", "pattern": "DIALOG.YESNO", "line": 14, "message": "waits for user choice"},
    {"severity": "block", "pattern": "INKEY", "line": 22, "message": "waits for keypress"},
    {"severity": "warn", "pattern": "WAIT", "line": 31, "message": "unbounded wait"},
    {"severity": "info", "pattern": "WINPOS", "line": 5, "message": "no effect in headless mode"}
  ]
}
```

Classification rules:

- `unsafe_for_headless`: any `block`-severity pattern present
- `needs_manual_rewrite`: no `block` patterns but `warn` patterns present, or quality checks fail
- `safe`: no `block` or `warn` patterns and all quality checks pass

#### mode=report: full conversion report with severity classes

Includes everything from `check` plus the LSP-side quality checks:

```json
{
  "classification": "needs_manual_rewrite",
  "patterns": [ ... ],
  "quality": {
    "has_screen_off": false,
    "has_area_setup": false,
    "has_error_handler": true,
    "has_metadata": false,
    "has_enddo_return": true,
    "parse_valid": true,
    "gui_violations": ["DIALOG.YESNO at line 14"]
  },
  "issues": [
    {"severity": "error", "check": "gui_keyword", "message": "DIALOG.YESNO found at line 14", "line": 14},
    {"severity": "error", "check": "screen_off", "message": "Missing SCREEN.OFF command"},
    {"severity": "error", "check": "area_setup", "message": "Missing AREA.Create/Select setup"},
    {"severity": "warn", "check": "metadata", "message": "Missing @target: metadata header"}
  ],
  "issue_count": 4
}
```

Severity classes for quality issues:

- `error`: will cause headless failure or silent misbehavior (GUI keywords, missing SCREEN.OFF, missing AREA setup)
- `warn`: reduces observability or safety (missing error handler, missing metadata, missing ENDDO return)
- `info`: cosmetic or best-practice (missing documentation headers)

#### mode=suggest: report + suggested rewrites per pattern

Includes everything from `report` plus per-pattern rewrite suggestions:

```json
{
  "classification": "unsafe_for_headless",
  "patterns": [ ... ],
  "quality": { ... },
  "issues": [ ... ],
  "suggestions": [
    {
      "pattern": "DIALOG.YESNO",
      "line": 14,
      "original": "DIALOG.YESNO \"Erase flash?\"",
      "suggested": "ENTRY &confirm\nIF \"&confirm\"!=\"true\"\n(\n  PRINT \"flash erase skipped\"\n  ENDDO\n)",
      "note": "Replace dialog with ENTRY parameter; pass confirm=true from MCP tool arguments"
    },
    {
      "pattern": "INKEY",
      "line": 22,
      "original": "INKEY &key",
      "suggested": "ENTRY &key\nIF \"&key\"==\"\"\n(\n  PRINT %ERROR \"missing parameter: key\"\n  ENDDO\n)",
      "note": "Replace keypress wait with ENTRY parameter"
    }
  ],
  "wrapper_available": true
}
```

Suggested rewrite patterns follow the manual conversion cookbook already documented in this research (ENTRY for input, explicit values for dialogs, logged checkpoints for pauses, bounded waits, AREA routing).

### Integration with existing blocking detection in session_tools.spl

The T32 MCP `session_tools.spl` already has these blocking-related functions:

- `t32_check_blocking(text_to_scan)` -- returns `[text]` of `BLOCK:`/`WARN:`/`INFO:` prefixed warnings
- `t32_has_blocking(warnings)` -- returns `true` if any warning starts with `BLOCK:`
- `t32_blocking_result(id, command, warnings)` -- constructs JSON error response with `blocked=true`, warnings array, and hint
- `t32_scan_cmm_file(path)` -- reads a file and runs `t32_check_blocking` on its content

The proposed `t32_cmm_validate` tool should:

1. **Reuse `t32_check_blocking`** for pattern detection, but parse the prefix (`BLOCK:`/`WARN:`/`INFO:`) into structured severity fields and extract line numbers by scanning the source line-by-line rather than as a flat string.

2. **Import the LSP-side checks** from `cmm_validate_cli` (GUI keyword check via `check_gui_keywords`, `SCREEN.OFF` presence, AREA setup, error handler, metadata headers, ENDDO return, parse validation). These should be factored into a shared module importable by both LSP MCP and T32 MCP.

3. **Wire into `t32_cmm_run` pre-flight.** When `cli_safe=true` is passed to `t32_cmm_run`, the handler should call `t32_cmm_validate(source, mode: "check")` and reject scripts classified as `unsafe_for_headless`, returning the structured report instead of the current flat warning array.

4. **Preserve `force=true` escape.** The existing `force` parameter should still bypass both blocking detection and validation, for cases where the user knows the script is safe despite triggering patterns.

### Wrapper template generation for parameterized scripts

When `mode=suggest` and the script has identifiable input points (DIALOG, INKEY, ENTER patterns), the tool should optionally generate a wrapper template:

```cmm
; Auto-generated CLI-safe wrapper for: original_script.cmm
; Parameters extracted from interactive patterns
ENTRY &param1 &param2 &confirm

; Validate required parameters
IF "&param1"==""
(
  PRINT %ERROR "missing parameter: param1"
  ENDDO FALSE()
)

; Headless setup
SCREEN.OFF
AREA.Create MCP_OUT
AREA.Select MCP_OUT
ON ERROR GOTO cleanup

; Call original with parameters
DO original_script.cmm &param1 &param2

ENDDO TRUE()

cleanup:
PRINT %ERROR "script failed"
ENDDO FALSE()
```

The wrapper template generation should:

- extract parameter names from DIALOG/INKEY/ENTER patterns
- add ENTRY with all extracted parameters
- add parameter validation
- add headless boilerplate (SCREEN.OFF, AREA setup, ON ERROR)
- call the original script via DO with parameters where possible
- include ENDDO with return values

This is boilerplate generation only. It does not attempt semantic rewriting of the original script's internal logic.

## Test Coverage Assessment

### Coverage matrix

| Component | Unit | Feature | Integration | System | Total Spec Files |
|-----------|------|---------|-------------|--------|-----------------|
| **T32 MCP core** | 5 (dispatch, json, run_guard, schema, state_diff) | 5 (mcp, tools, guard, bugfix, lsp_mcp) | -- | 1 (lifecycle) | 11 |
| **T32 CLI** | 9 (catalog_loader, error_codes, error_messages, session, shell, catalog, text_parser, window_parsers, window_model) | 1 (t32_cli) | -- | -- | 10 |
| **T32 GDB/debug** | 5 (register_t32_gdb, t32_gdb_adapter, t32_gdb_bridge_flow, t32_gdb_bridge, t32_native_flow) | -- | 2 (t32_gdb_bridge, t32_native) | -- | 7 |
| **CMM GUI** | -- | 1 (t32_cmm_gui) | -- | 1 (t32_gui_system) | 2 |
| **CMM LSP** | ~25 files (parser, lexer, analyzer, commands, completions, hover, symbols) | 1 (t32_lsp_mcp) | -- | -- | ~26 |
| **Debug/DAP general** | 10+ (debug_*, dap_*) | 6 (dap, breakpoint, state, integration, stack_trace, step_modes) | 12 (debug_trace_integration 1-10, hardware) | -- | ~28 |
| **MCP general** | 10+ (fileio, api_tool, argument_parsing, capabilities, command_filter, coordinator, ...) | 5+ (mcp core, handler_registry, helpers, schema, protocol) | 3 (stdio, bugdb, debug_log_tree) | -- | ~18 |

**Interpreter mode limitation**: The test runner in interpreter mode only verifies that spec files load without errors. The `it` block bodies do not execute. This means all tests listed above confirm module structure and import correctness but do not exercise runtime behavior unless run in compiled mode.

### Gaps needing new tests

#### Job manager (proposed Phase 1)

No test coverage exists yet. Required:

- **Unit**: `mcp_t32_job_manager_spec.spl` -- job creation, status transitions (queued -> running -> completed/failed/timed_out/cancelled), job retention and cleanup, concurrent job limits
- **Unit**: `mcp_t32_job_list_spec.spl` -- list filtering by session/status, job_get by id, job_cancel behavior
- **Feature**: `t32_mcp_async_spec.spl` -- background launch via `background=true`, foreground wait with timeout, timeout-to-job promotion, resource reads for job results
- **Integration**: requires live T32 or mock backend for real async script execution

#### Window snapshots (proposed Phase 1)

Partial coverage exists in `window_parsers_spec.spl` and `window_model_spec.spl` for parsing. Missing:

- **Unit**: `mcp_t32_window_snapshot_spec.spl` -- snapshot storage, hash comparison, diff generation, structured row diff, table/cell diff, fallback text diff
- **Feature**: `t32_mcp_window_diff_spec.spl` -- `mode=summary|diff|full` parameter behavior, `since_last` tracking, first-capture-returns-full behavior
- **Integration**: window capture with diff across command sequences

#### CMM validator MCP exposure (proposed Phase 2)

The LSP-side `cmm_validate_cli` has implicit coverage through `t32_lsp_mcp_spec.spl`. The T32 MCP side needs:

- **Unit**: `mcp_t32_cmm_validate_spec.spl` -- mode=check classification logic, mode=report quality checks, mode=suggest rewrite generation, wrapper template generation
- **Unit**: shared validator module tests if checks are factored out of LSP
- **Feature**: `t32_mcp_validator_spec.spl` -- end-to-end validation from MCP tool call through to structured report
- **Integration**: validate -> rewrite -> execute workflow with mock T32 backend

#### Async tools and timeouts (proposed Phase 1)

- **Unit**: `mcp_t32_timeout_spec.spl` -- per-tool timeout defaults, per-call override, timeout class behavior (connect, command, practice_wait, window_capture, job_retention)
- **Feature**: `t32_mcp_status_snapshot_spec.spl` -- `t32_status_snapshot` tool returning run_state, system info, message line
- **Integration**: timeout behavior with real or mocked T32 backend timing

### Test strategy

| Level | Purpose | T32 Required | Run Mode | Frequency |
|-------|---------|--------------|----------|-----------|
| **Unit** | Validate individual functions (blocking detection, JSON construction, classification logic, diff algorithms) | No | Compiled preferred, interpreter for load-check | Every commit |
| **Feature** | Validate tool-level behavior with mocked backends (tool dispatch, parameter validation, mode switching, report structure) | No | Compiled | Every commit |
| **Integration** | Validate end-to-end workflows with real or simulated T32 (connect -> validate -> run -> capture -> diff) | Yes (or mock) | Compiled | Pre-release, CI with T32 simulator |
| **System/Live** | Validate full MCP lifecycle with real TRACE32 hardware connection | Yes (hardware) | Compiled | Manual, pre-release only |

Unit and feature tests should mock the T32 backend (`t32_run_remote` returns canned responses). Integration tests should use either a T32 simulator instance or a real connection with a known target state. System tests are inherently manual due to hardware dependency.

For the interpreter mode limitation, critical behavioral tests (job state transitions, diff correctness, classification logic) should be verified in compiled mode during CI. Interpreter mode serves as a fast smoke test for import correctness and module structure.

## Integration with MCP/LSP/DAP Roadmap

### Phase alignment

The main MCP/LSP/DAP roadmap (`doc/01_research/mcp_lsp_dap_integration_analysis.md`) defines 6 phases over 19-27 weeks. The T32 MCP roadmap defined earlier in this document has 3 phases. Here is how they align:

| Main Roadmap Phase | Duration | T32 MCP Phase | Relationship |
|--------------------|----------|---------------|-------------|
| **Phase 1: Shared Infrastructure** (Compiler Query API + Interpreter Hooks) | 4-6 weeks | -- | No direct dependency. T32 MCP does not use the Simple compiler query API. Phase 1 tasks are all marked complete. |
| **Phase 2: MCP Enhancement** (Resources + Prompts) | 2-3 weeks | **T32 Phase 1** (job manager, async, snapshots, resources) | **Strong overlap.** Both add resource management and structured content patterns. T32 MCP already has resources; main MCP is adding the Resource Management API. |
| **Phase 3: LSP Phase 2** (Completion, Hover, Goto) | 3-4 weeks | **T32 Phase 2** (CMM validator, wrapper templates) | **Parallel work.** CMM LSP features (completion, hover, symbols) improve alongside T32 MCP validator exposure. Shared CMM parser/analyzer code benefits both. |
| **Phase 4: DAP Phase 2** (Real debugging) | 2-3 weeks | -- | No direct dependency, but T32 GDB bridge integration could benefit from shared DAP infrastructure. |
| **Phase 5: LSP Phase 3** (References, Symbols) | 4-6 weeks | -- | CMM LSP symbols tool already exists; could contribute patterns back to main LSP. |
| **Phase 6: DAP Phase 3-4** (Evaluation, Watches) | 4-5 weeks | **T32 Phase 3** (MCP Tasks upgrade) | **Convergence point.** Both involve protocol upgrades and richer runtime interaction. |

Current status of each:

- **Main roadmap**: Phase 1 tasks are all marked complete (parser API, symbol table, type inference, error recovery, interpreter hooks, bytecode callbacks). Phases 2-6 are planned but not started. MCP is production-ready. LSP and DAP are Phase 1/4 complete (protocol layer only, mock data for DAP).
- **T32 MCP roadmap**: All three phases are planned. No implementation has started beyond the existing blocking detection, window capture infrastructure, and the gap analysis documented above.

### Shared infrastructure opportunities

1. **Protocol layer.** The main roadmap Phase 2 adds resource management and prompt templates to the core MCP implementation (`src/app/mcp/`). The T32 MCP server already implements resources independently in `t32_mcp/`. Once the main Resource Management API (`src/app/mcp/resources.spl`) is built, T32 MCP should adopt it rather than maintaining a parallel implementation. This reduces duplication and ensures consistent resource URI patterns across all MCP servers.

2. **Resource model.** The main roadmap proposes `ResourceManager` with static resources and dynamic templates. T32 MCP needs dynamic resources for `t32://jobs/<id>`, `t32://windows/<session>/<window>`, and `t32://sessions/<id>/status`. These are good candidates for the template-based resource system proposed in the main roadmap.

3. **Task system.** Both the main roadmap (Phase 6 timeframe) and T32 Phase 3 plan to adopt MCP `2025-11-25` Tasks. The internal job manager proposed for T32 Phase 1 should be designed as a protocol-agnostic layer that can back both current polling/resource patterns and future Task protocol adapters. The main roadmap should define the shared task abstraction; T32 MCP should be the first consumer.

4. **JSON-RPC infrastructure.** Both servers share JSON-RPC 2.0 over stdio. The main MCP already has this infrastructure. T32 MCP has its own JSON construction helpers (`t32_LB`, `t32_RB`, `t32_jp`, `t32_js`, `t32_jo2`, `t32_jo3`, etc.). A shared JSON builder module would reduce code duplication across MCP servers.

5. **Diagnostic model.** The main LSP implementation uses `publishDiagnostics` for parse errors. The CMM LSP uses its own diagnostic model via `cmm_diagnostics`. If the CMM LSP diagnostics are aligned with the main LSP diagnostic format, the CMM validator MCP tool can reuse the same structured output format for its quality issues.

### Recommended integration points

1. **T32 Phase 1 should start during or after Main Phase 2.** Main Phase 2 delivers the Resource Management API that T32 MCP should adopt. Starting T32 Phase 1 concurrently is acceptable if T32 resources are built against the planned API shape, with a migration step after Main Phase 2 completes.

2. **T32 Phase 2 should coordinate with Main Phase 3.** Both involve LSP-adjacent work. The CMM parser/analyzer used by `cmm_validate_cli` and the CMM LSP tools (`cmm_parse`, `cmm_diagnostics`, `cmm_complete`, `cmm_hover`, `cmm_symbols`) should be factored into a shared `cmm_analysis` module that both the LSP MCP and the T32 MCP import. Main Phase 3 work on the Simple LSP can inform patterns for the CMM LSP.

3. **T32 Phase 3 should merge with Main Phase 6.** Both target MCP `2025-11-25` Tasks adoption. The protocol upgrade should happen once, across all MCP servers, with a shared task adapter layer.

4. **T32 GDB bridge should feed into Main Phase 4.** The T32 GDB bridge (tested in `t32_gdb_bridge_spec.spl`, `t32_gdb_adapter_spec.spl`) already implements GDB remote protocol handling. When Main Phase 4 builds real DAP integration with interpreter hooks, the T32 GDB bridge can serve as a second DAP backend (remote hardware debugging via T32) alongside the primary backend (local Simple interpreter debugging).

### Combined timeline

| Week | Main Roadmap | T32 MCP | Integration Notes |
|------|-------------|---------|-------------------|
| 1-6 | Phase 1: Shared Infrastructure (complete) | -- | Foundation already complete |
| 7-9 | Phase 2: MCP Enhancement | **T32 Phase 1 start**: job manager, async split, timeouts, status snapshot | T32 adopts Resource Management API shape from Main Phase 2 |
| 10-12 | Phase 2 wrap-up | **T32 Phase 1 continued**: window snapshots, diff model, resource-backed payloads | Shared resource patterns stabilize |
| 13-16 | Phase 3: LSP Phase 2 | **T32 Phase 2**: CMM validator MCP, wrapper templates, watched-window policy | Shared CMM analysis module; CMM LSP and T32 MCP import same parser |
| 17-19 | Phase 4: DAP Phase 2 | T32 Phase 2 wrap-up | T32 GDB bridge informs DAP backend patterns |
| 20-25 | Phase 5: LSP Phase 3 | -- | CMM LSP symbols already implemented |
| 26-30 | Phase 6: DAP Phase 3-4 | **T32 Phase 3**: MCP Tasks upgrade | Shared task adapter; protocol upgrade happens once for all servers |

Total combined timeline: approximately 30 weeks. T32 MCP phases interleave with main roadmap phases rather than running as an independent track. The key constraint is that T32 Phase 1 should not start before Main Phase 2 Resource Management API design is at least sketched, to avoid building a parallel resource system that must be rewritten.

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
