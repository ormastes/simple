# T32 MCP-CLI Improvements — Module Design

**Date:** 2026-03-25
**Status:** Draft
**Requirement:** doc/requirement/t32_mcp_cli_improvements.md
**Research:** doc/01_research/t32_mcp_cli_async_and_window_ux.md
**Plan:** doc/03_plan/t32_mcp_cli_improvements.md

## File Layout

### New Files

| File | Feature | Purpose |
|------|---------|---------|
| `t32_mcp/job_manager.spl` | F1 | T32Job class, T32JobManager, state machine, poll logic |
| `t32_mcp/job_tools.spl` | F1 | Tool handlers: t32_job_list, t32_job_get, t32_job_cancel, t32_job_result |
| `t32_mcp/snapshot_store.spl` | F2 | T32WindowSnapshot, T32SnapshotStore, T32DiffEntry, diff engine |
| `t32_mcp/cmm_validator.spl` | F4 | Blocking-pattern detection, severity classification, rewrite suggestions |
| `test/examples/t32_mcp/job_manager_spec.spl` | F1 | SPipe tests for job lifecycle |
| `test/examples/t32_mcp/snapshot_store_spec.spl` | F2 | SPipe tests for snapshot/diff |
| `test/examples/t32_mcp/cmm_validator_spec.spl` | F4 | SPipe tests for CMM validation |
| `test/examples/t32_mcp/gap_tools_spec.spl` | F3 | SPipe tests for session_info, action_list, status_snapshot |
| `test/examples/t32_mcp/impl_fixes_spec.spl` | F5 | SPipe tests for dict lookup, retry, SDN error, timeouts |

### Modified Files

| File | Feature | Changes |
|------|---------|---------|
| `t32_mcp/main.spl` | F1,F2 | Add `use` for job_manager, snapshot_store, cmm_validator modules |
| `t32_mcp/session_tools.spl` | F1,F3,F5 | Add background param to cmm_run/cmd_run; add session_info/status_snapshot handlers; add retry to session_open; add timeout_ms params |
| `t32_mcp/window_tools.spl` | F2,F5 | Integrate snapshot store into window_capture; add mode param; add timeout_ms; fix SDN error reporting |
| `t32_mcp/action_tools.spl` | F3,F5 | Add action_list handler; replace O(N) field lookup with Dict; update dispatcher for new tools |
| `t32_mcp/protocol.spl` | F1-F4 | Register all new tools in schema list and tool list |
| `t32_mcp/headless_tools.spl` | F4 | Extract blocking patterns into shared cmm_validator.spl |

All paths relative to `examples/10_tooling/trace32_tools/`.

---

## Class Definitions

### F1: T32Job (job_manager.spl)

```simple
class T32Job:
    job_id: text                  # "j1", "j2", ... monotonic counter
    tool_name: text               # "t32_cmm_run", "t32_cmd_run"
    session_id: text              # owning McpT32Session.id
    core_id: text                 # core selected at launch time
    status: text                  # state machine value (see diagram)
    started_at: i64               # unix microseconds
    updated_at: i64               # unix microseconds, refreshed each poll
    timeout_ms: i64               # max background lifetime; 0 = no limit
    poll_interval_ms: i64         # recommended poll interval for clients
    summary: text                 # human-readable one-liner
    result: text                  # captured output (AREA text, command output)
    error: text                   # error message if failed/timed_out
    resource_uri: text            # "t32:///jobs/j1"
    _script_path: text            # CMM script path (cmm_run jobs)
    _command: text                # raw command (cmd_run jobs)
    _last_practice_state: text    # last PRACTICE.STATE() value
    _area_name: text              # AREA window to capture on completion

    fn elapsed_ms() -> i64:
        (self.updated_at - self.started_at) / 1000

    fn is_terminal() -> bool:
        (self.status == "completed" or self.status == "failed" or
         self.status == "timed_out" or self.status == "cancelled")

    fn to_summary_json() -> text:
        var r = t32_LB()
        r = r + t32_jp("job_id", t32_js(self.job_id))
        r = r + "," + t32_jp("tool_name", t32_js(self.tool_name))
        r = r + "," + t32_jp("status", t32_js(self.status))
        r = r + "," + t32_jp("elapsed_ms", str(self.elapsed_ms()))
        r = r + "," + t32_jp("summary", t32_js(self.summary))
        r = r + t32_RB()
        r

    fn to_detail_json() -> text:
        var r = t32_LB()
        r = r + t32_jp("job_id", t32_js(self.job_id))
        r = r + "," + t32_jp("tool_name", t32_js(self.tool_name))
        r = r + "," + t32_jp("session_id", t32_js(self.session_id))
        r = r + "," + t32_jp("core_id", t32_js(self.core_id))
        r = r + "," + t32_jp("status", t32_js(self.status))
        r = r + "," + t32_jp("elapsed_ms", str(self.elapsed_ms()))
        r = r + "," + t32_jp("summary", t32_js(self.summary))
        r = r + "," + t32_jp("result_available", if self.is_terminal() and self.result != "": "true" else: "false")
        r = r + "," + t32_jp("resource_uri", t32_js(self.resource_uri))
        if self.error != "":
            r = r + "," + t32_jp("error", t32_js(self.error))
        r = r + t32_RB()
        r
```

### F1: T32JobManager (job_manager.spl)

```simple
# --- Module-level state ---
var T32_JOBS: [T32Job] = []
var T32_NEXT_JOB_ID: i64 = 1
val T32_MAX_CONCURRENT_JOBS: i64 = 16
val T32_JOB_RETENTION_MS: i64 = 300000   # 5 minutes
val T32_DEFAULT_POLL_MS: i64 = 500

class T32JobManager:
    # Stateless — operates on module-level state.
    # Matches existing MCP pattern (BG_TASKS is module-level).

    static fn create_job(tool_name: text, session_id: text, core_id: text,
                         timeout_ms: i64) -> Result<T32Job, text>:
        T32JobManager.cleanup_if_needed()
        val active = T32JobManager.count_active()
        if active >= T32_MAX_CONCURRENT_JOBS:
            return Err("max concurrent jobs ({T32_MAX_CONCURRENT_JOBS}) reached")
        val jid = "j" + str(T32_NEXT_JOB_ID)
        T32_NEXT_JOB_ID = T32_NEXT_JOB_ID + 1
        val now = rt_time_now_unix_micros()
        var job = T32Job(
            job_id: jid, tool_name: tool_name,
            session_id: session_id, core_id: core_id,
            status: "queued", started_at: now, updated_at: now,
            timeout_ms: timeout_ms, poll_interval_ms: T32_DEFAULT_POLL_MS,
            summary: "", result: "", error: "",
            resource_uri: "t32:///jobs/" + jid,
            _script_path: "", _command: "",
            _last_practice_state: "", _area_name: ""
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
        T32JobManager.cleanup()
        T32_JOBS

    static fn cancel_job(job_id: text) -> Result<T32Job, text>:
        var i = 0
        while i < T32_JOBS.len():
            var job = T32_JOBS[i]
            if job.job_id == job_id:
                if job.is_terminal():
                    return Err("job {job_id} already terminal: {job.status}")
                job.status = "cancelled"
                job.updated_at = rt_time_now_unix_micros()
                job.summary = "cancelled by client"
                T32_JOBS[i] = job
                return Ok(job)
            i = i + 1
        Err("job not found: {job_id}")

    static fn poll_all():
        val now = rt_time_now_unix_micros()
        var i = 0
        while i < T32_JOBS.len():
            var job = T32_JOBS[i]
            if not job.is_terminal():
                val updated = T32JobManager.poll_one(job, now)
                if updated.status != job.status or updated.updated_at != job.updated_at:
                    T32_JOBS[i] = updated
            i = i + 1

    static fn poll_one(job: T32Job, now: i64) -> T32Job:
        # Timeout check
        val elapsed = (now - job.started_at) / 1000
        if job.timeout_ms > 0 and elapsed > job.timeout_ms:
            job.status = "timed_out"
            job.updated_at = now
            job.error = "timed out after {elapsed}ms (limit: {job.timeout_ms}ms)"
            return job
        # Session lookup
        val session = t32_find_session(job.session_id)
        if session.?:
            match job.status:
                "running":
                    # Dispatch to waiting_practice or waiting_target
                    val pstate = t32_poll_practice_state_remote(session!, job)
                    if pstate != "0" and pstate != "idle":
                        job.status = "waiting_practice"
                    else:
                        val target_running = t32_query_state_run(session!)
                        if target_running:
                            job.status = "waiting_target"
                        else:
                            job.status = "completed"
                            job.summary = "completed immediately"
                    job.updated_at = now
                "waiting_practice":
                    val state = t32_poll_practice_state_remote(session!, job)
                    job._last_practice_state = state
                    if state == "0" or state == "idle":
                        job.status = "completed"
                        job.result = t32_capture_area(session!, job._area_name)
                        job.summary = "practice done after {elapsed}ms"
                    elif state == "dialog":
                        job.status = "failed"
                        job.error = "PRACTICE entered dialog state (headless hang)"
                    job.updated_at = now
                "waiting_target":
                    val running = t32_query_state_run(session!)
                    if not running:
                        job.status = "completed"
                        job.summary = "target stopped after {elapsed}ms"
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
            if not job.is_terminal() or (now - job.updated_at) < retention_us:
                kept = kept + [job]
        T32_JOBS = kept

    static fn cleanup_if_needed():
        if T32_JOBS.len() > T32_MAX_CONCURRENT_JOBS * 2:
            T32JobManager.cleanup()

    static fn count_active() -> i64:
        var n: i64 = 0
        for job in T32_JOBS:
            if not job.is_terminal():
                n = n + 1
        n
```

### F1: Job Status State Machine

```
                          ┌─────────────────────────────────────────┐
                          │                                         │
    ┌────────┐     ┌──────┴──┐     ┌──────────────────┐     ┌──────┴─────┐
    │ queued ├────>│ running ├────>│ waiting_practice ├────>│ completed  │
    └────────┘     │         ├────>│                  │     └────────────┘
                   │         │     └────────┬─────────┘           ^
                   │         │              │                     │
                   │         │              v                     │
                   │         │     ┌──────────────────┐           │
                   │         ├────>│ waiting_target   ├───────────┘
                   │         │     └──────────────────┘
                   │         │
                   └────┬────┘
                        │
              ┌─────────┼──────────┐
              v         v          v
        ┌─────────┐ ┌────────┐ ┌───────────┐
        │ failed  │ │timed_  │ │ cancelled │
        │         │ │  out   │ │           │
        └─────────┘ └────────┘ └───────────┘
```

**Transition rules:**
- `queued` -> `running`: job manager sends command to T32, gets acknowledgement
- `running` -> `waiting_practice`: `PRACTICE.STATE()` returns non-zero (script executing)
- `running` -> `waiting_target`: `STATE.RUN()` returns true (target running)
- `running` -> `completed`: command completes immediately
- `waiting_practice` -> `completed`: `PRACTICE.STATE()` returns 0 (idle)
- `waiting_practice` -> `failed`: `PRACTICE.STATE()` returns "dialog" or error
- `waiting_target` -> `completed`: `STATE.RUN()` returns false (target stopped)
- any non-terminal -> `timed_out`: elapsed exceeds `timeout_ms` (when `timeout_ms > 0`)
- any non-terminal -> `cancelled`: client calls `t32_job_cancel`

**Terminal states:** `completed`, `failed`, `timed_out`, `cancelled`

---

### F2: T32WindowSnapshot (snapshot_store.spl)

```simple
class T32WindowSnapshot:
    key: text                     # window key (e.g. "register", "data.dump")
    session_id: text              # owning session
    core_id: text                 # core at capture time
    title: text                   # window title
    content: text                 # full captured text
    structured_rows: [text]       # parsed "label|value" rows (empty if non-structured)
    hash: i64                     # djb2 hash of content
    captured_at: i64              # unix microseconds

    fn to_json() -> text:
        var r = t32_LB()
        r = r + t32_jp("key", t32_js(self.key))
        r = r + "," + t32_jp("title", t32_js(self.title))
        r = r + "," + t32_jp("hash", str(self.hash))
        r = r + "," + t32_jp("captured_at", str(self.captured_at))
        r = r + "," + t32_jp("row_count", str(self.structured_rows.len()))
        r = r + t32_RB()
        r
```

### F2: T32DiffEntry (snapshot_store.spl)

```simple
class T32DiffEntry:
    label: text                   # row label or line number
    old_value: text               # previous value
    new_value: text               # current value
    diff_type: text               # "changed", "added", "removed"

    fn to_json() -> text:
        var r = t32_LB()
        r = r + t32_jp("label", t32_js(self.label))
        r = r + "," + t32_jp("old", t32_js(self.old_value))
        r = r + "," + t32_jp("new", t32_js(self.new_value))
        r = r + "," + t32_jp("type", t32_js(self.diff_type))
        r = r + t32_RB()
        r
```

### F2: T32SnapshotStore (snapshot_store.spl)

```simple
# --- Module-level state ---
var T32_SNAPSHOTS: [T32WindowSnapshot] = []
val T32_SNAPSHOT_MAX_ENTRIES: i64 = 200
val T32_SNAPSHOT_TTL_MS: i64 = 300000    # 5 minutes
val T32_TOKEN_BUDGET_WARN: i64 = 8000    # warn when diff exceeds this
val T32_TOKEN_BUDGET_MAX: i64 = 10000    # hard cap

class T32SnapshotStore:
    # Stateless — operates on module-level T32_SNAPSHOTS.

    static fn store(session_id: text, core_id: text, key: text,
                    title: text, content: text) -> T32WindowSnapshot:
        val hash = t32_djb2_hash(content)
        val rows = t32_parse_structured_rows(content)
        val now = rt_time_now_unix_micros()
        val snap = T32WindowSnapshot(
            key: key, session_id: session_id, core_id: core_id,
            title: title, content: content, structured_rows: rows,
            hash: hash, captured_at: now
        )
        # Evict oldest if at cap
        T32SnapshotStore.evict_if_needed()
        # Replace existing or append
        var replaced = false
        var i = 0
        while i < T32_SNAPSHOTS.len():
            val s = T32_SNAPSHOTS[i]
            if s.session_id == session_id and s.core_id == core_id and s.key == key:
                T32_SNAPSHOTS[i] = snap
                replaced = true
                break
            i = i + 1
        if not replaced:
            T32_SNAPSHOTS = T32_SNAPSHOTS + [snap]
        snap

    static fn get(session_id: text, core_id: text, key: text) -> Option<T32WindowSnapshot>:
        for s in T32_SNAPSHOTS:
            if s.session_id == session_id and s.core_id == core_id and s.key == key:
                return Some(s)
        nil

    static fn diff(old_snap: T32WindowSnapshot, new_content: text) -> (bool, [T32DiffEntry]):
        val new_hash = t32_djb2_hash(new_content)
        if old_snap.hash == new_hash:
            return (false, [])
        # Try structured diff first
        val new_rows = t32_parse_structured_rows(new_content)
        if old_snap.structured_rows.len() > 0 and new_rows.len() > 0:
            val entries = t32_structured_row_diff(old_snap.structured_rows, new_rows)
            return (true, entries)
        # Fall back to text diff
        val entries = t32_text_line_diff(old_snap.content, new_content)
        (true, entries)

    static fn evict_if_needed():
        # Evict by TTL
        val now = rt_time_now_unix_micros()
        val ttl_us = T32_SNAPSHOT_TTL_MS * 1000
        var kept: [T32WindowSnapshot] = []
        for s in T32_SNAPSHOTS:
            if (now - s.captured_at) < ttl_us:
                kept = kept + [s]
        T32_SNAPSHOTS = kept
        # Evict oldest if still over cap
        while T32_SNAPSHOTS.len() >= T32_SNAPSHOT_MAX_ENTRIES:
            # Remove oldest by captured_at
            var oldest_idx = 0
            var oldest_time = T32_SNAPSHOTS[0].captured_at
            var i = 1
            while i < T32_SNAPSHOTS.len():
                if T32_SNAPSHOTS[i].captured_at < oldest_time:
                    oldest_idx = i
                    oldest_time = T32_SNAPSHOTS[i].captured_at
                i = i + 1
            # Remove at index
            var new_list: [T32WindowSnapshot] = []
            var j = 0
            while j < T32_SNAPSHOTS.len():
                if j != oldest_idx:
                    new_list = new_list + [T32_SNAPSHOTS[j]]
                j = j + 1
            T32_SNAPSHOTS = new_list

# --- Hashing ---

fn t32_djb2_hash(s: text) -> i64:
    var hash: i64 = 5381
    var i = 0
    while i < s.len():
        val ch = s.char_code_at(i)
        hash = ((hash * 33) + ch) % 2147483647   # keep in i64 range
        i = i + 1
    hash

# --- Structured row parsing ---
# Parses windows with "label  value" or "label: value" format
# into "label|value" pipe-delimited strings.

fn t32_parse_structured_rows(content: text) -> [text]:
    var rows: [text] = []
    val lines = content.split("\n")
    for line in lines:
        val trimmed = line.trim()
        if trimmed.len() == 0:
            continue
        # Try "label: value" format
        val colon_idx = t32_find_colon(trimmed)
        if colon_idx > 0 and colon_idx < trimmed.len() - 1:
            val label = trimmed.substring(0, colon_idx).trim()
            val value = trimmed.substring(colon_idx + 1).trim()
            if label.len() > 0:
                rows.push(label + "|" + value)
                continue
        # Try "LABEL  VALUE" format (2+ spaces as separator)
        val parts = t32_split_multi_space(trimmed)
        if parts.len() == 2:
            rows.push(parts[0] + "|" + parts[1])
            continue
    rows

fn t32_split_multi_space(s: text) -> [text]:
    # Split on 2+ consecutive spaces
    var parts: [text] = []
    var current = ""
    var space_count = 0
    var i = 0
    while i < s.len():
        if s[i] == " ":
            space_count = space_count + 1
        else:
            if space_count >= 2 and current.len() > 0:
                parts.push(current.trim())
                current = ""
            elif space_count > 0:
                current = current + " "
            current = current + s[i]
            space_count = 0
        i = i + 1
    if current.trim().len() > 0:
        parts.push(current.trim())
    parts

# --- Diff engines ---

fn t32_structured_row_diff(old_rows: [text], new_rows: [text]) -> [T32DiffEntry]:
    var entries: [T32DiffEntry] = []
    # Build label->value map from old rows
    var old_labels: [text] = []
    var old_values: [text] = []
    for row in old_rows:
        val parts = row.split("|")
        if parts.len() >= 2:
            old_labels = old_labels + [parts[0]]
            old_values = old_values + [parts[1]]
    # Compare against new rows
    for row in new_rows:
        val parts = row.split("|")
        if parts.len() < 2:
            continue
        val label = parts[0]
        val new_val = parts[1]
        var found = false
        var i = 0
        while i < old_labels.len():
            if old_labels[i] == label:
                found = true
                if old_values[i] != new_val:
                    entries = entries + [T32DiffEntry(
                        label: label, old_value: old_values[i],
                        new_value: new_val, diff_type: "changed"
                    )]
                break
            i = i + 1
        if not found:
            entries = entries + [T32DiffEntry(
                label: label, old_value: "",
                new_value: new_val, diff_type: "added"
            )]
    # Check for removed rows
    for row in old_rows:
        val parts = row.split("|")
        if parts.len() < 2:
            continue
        val label = parts[0]
        var found = false
        for new_row in new_rows:
            val new_parts = new_row.split("|")
            if new_parts.len() >= 2 and new_parts[0] == label:
                found = true
                break
        if not found:
            entries = entries + [T32DiffEntry(
                label: label, old_value: parts[1],
                new_value: "", diff_type: "removed"
            )]
    entries

fn t32_text_line_diff(old_text: text, new_text: text) -> [T32DiffEntry]:
    # Simple line-by-line diff with context
    var entries: [T32DiffEntry] = []
    val old_lines = old_text.split("\n")
    val new_lines = new_text.split("\n")
    val max_len = if old_lines.len() > new_lines.len(): old_lines.len() else: new_lines.len()
    var i = 0
    while i < max_len:
        val old_line = if i < old_lines.len(): old_lines[i] else: ""
        val new_line = if i < new_lines.len(): new_lines[i] else: ""
        if old_line != new_line:
            val label = "L" + str(i + 1)
            val dtype = if i >= old_lines.len(): "added"
                        elif i >= new_lines.len(): "removed"
                        else: "changed"
            entries = entries + [T32DiffEntry(
                label: label, old_value: old_line,
                new_value: new_line, diff_type: dtype
            )]
        i = i + 1
    entries
```

---

## API Surface — New MCP Tools

### F1: Job Tools (job_tools.spl)

#### t32_job_list

```
Parameters: (none)
Returns:
  { jobs: [{ job_id, tool_name, status, elapsed_ms, summary }] }
Side effects: triggers poll_all() + cleanup()
Annotations: readOnlyHint=true, idempotentHint=true
```

#### t32_job_get

```
Parameters:
  job_id: text (required) — job identifier ("j1", "j2", ...)
Returns:
  { job_id, tool_name, session_id, core_id, status, elapsed_ms,
    summary, result_available, resource_uri, error? }
Side effects: triggers poll_all()
Annotations: readOnlyHint=true, idempotentHint=true
```

#### t32_job_cancel

```
Parameters:
  job_id: text (required) — job identifier
Returns:
  { job_id, status: "cancelled", summary: "cancelled by client" }
Error: job not found, or job already in terminal state
Annotations: destructiveHint=true
```

#### t32_job_result

```
Parameters:
  job_id: text (required) — job identifier
Returns:
  { job_id, status, result } — result text or "still running" message
Error: job not found
Annotations: readOnlyHint=true
```

### F1: Modified Existing Tools

#### t32_cmm_run (modified — session_tools.spl)

```
New parameters:
  background: bool (optional, default false)
  timeout_ms: i64 (optional, default 30000)
Behavior when background=true:
  - Creates T32Job, fires script, returns immediately
  - Response: { job_id, status: "waiting_practice", tool_name, pollInterval: 2 }
Behavior when foreground times out:
  - Escalates to background job
  - Response: { job_id, status: "running", summary: "foreground timed out, continuing" }
```

#### t32_cmd_run (modified — session_tools.spl)

```
New parameters:
  background: bool (optional, default false)
  timeout_ms: i64 (optional, default 5000)
Behavior: same as t32_cmm_run when background=true
  For commands classified as immediate, background=true is ignored
```

### F2: Modified Window Capture

#### t32_window_capture (modified — window_tools.spl)

```
New parameters:
  mode: text (optional, default "diff") — "summary" | "diff" | "full"
  timeout_ms: i64 (optional, default 5000)
Returns (mode=summary):
  { window, title, changed: bool, change_count: i64, summary: text }
Returns (mode=diff, first capture):
  { window, title, changed: true, content: text }
Returns (mode=diff, unchanged):
  { window, title, changed: false }
Returns (mode=diff, changed):
  { window, title, changed: true, change_count: i64,
    window_diff: [{ label, old, new, type }],
    full_resource_uri: "t32:///windows/<session>/<window>" }
Returns (mode=full):
  { window, title, changed: bool, content: text }
Token budget: diff response capped at T32_TOKEN_BUDGET_WARN (8K tokens);
  if diff exceeds T32_TOKEN_BUDGET_MAX (10K), return full with warning
```

### F3: New Gap-Closure Tools

#### t32_session_info (session_tools.spl)

```
Parameters:
  session_id: text (optional, defaults to current session)
Returns:
  { session_id, host, port, architecture, intercom_name, connected,
    cores: [{ core_id, label }], run_state: "running"|"stopped"|"unknown",
    status_summary: text }
Annotations: readOnlyHint=true, idempotentHint=true
```

#### t32_action_list (action_tools.spl)

```
Parameters:
  window: text (optional) — filter actions for a specific window
Returns:
  { actions: [{ key, label, type, window, template }] }
Annotations: readOnlyHint=true, idempotentHint=true
```

#### t32_status_snapshot (session_tools.spl)

```
Parameters:
  session_id: text (optional, defaults to current session)
Returns:
  { session_id, run_state: "running"|"stopped"|"unknown",
    system_state: text, practice_state: text,
    message_line: text }
Side effects: queries STATE.RUN(), PRACTICE.STATE(), captures SYStem.state window
Annotations: readOnlyHint=true
```

### F4: CMM Validator Tool

#### t32_cmm_validate (cmm_validator.spl)

```
Parameters:
  source: text (required) — CMM script source code
  mode: text (optional, default "check") — "check" | "report" | "suggest"
Returns (mode=check):
  { classification: "safe"|"needs_manual_rewrite"|"unsafe_for_headless",
    findings: [{ line, command, severity: "BLOCK"|"WARN"|"INFO", message }] }
Returns (mode=report):
  { classification, findings, summary: text,
    block_count, warn_count, info_count }
Returns (mode=suggest):
  { classification, findings_with_suggestions:
    [{ line, command, severity, message, suggestion: text }],
    summary: text }
Annotations: readOnlyHint=true, idempotentHint=true
```

**7 BLOCK-level patterns** (from research, matching cmm_validate_cli):
1. `DIALOG.OK` / `DIALOG.YESNO` / `DIALOG.FILE` / `DIALOG.DIR` / `DIALOG.STRING`
2. `INKEY`
3. `ENTER` (without AREA context)
4. `PAUSE`
5. `STOP`
6. `SCREEN.WAIT` (without explicit capture purpose)
7. Unbounded `WAIT` without timeout

---

## Integration Points

### session_tools.spl Changes

```simple
# REQ-F1-003: Add background param to handle_t32_cmm_run
fn handle_t32_cmm_run(id: text, body: text) -> text:
    # ... existing parameter extraction ...
    val background = t32_extract_field(body, "background") == "true"
    val timeout_ms_str = t32_extract_field(body, "timeout_ms")
    var timeout_ms: i64 = 30000
    if timeout_ms_str != "":
        timeout_ms = timeout_ms_str.to_i64() ?? 30000

    if background:
        val job_result = T32JobManager.create_job(
            "t32_cmm_run", session.id, MCP_T32_CURRENT_CORE, timeout_ms)
        match job_result:
            Err(msg): return t32_make_tool_error(id, -32602, msg)
            Ok(job):
                job._script_path = script
                job._area_name = MCP_T32_AREA_NAME
                t32_run_remote(session, "DO " + script)
                job.status = "waiting_practice"
                job.updated_at = rt_time_now_unix_micros()
                return t32_make_job_handle_response(id, job)
    # ... existing synchronous path (modified for timeout escalation) ...

# REQ-F5-002: Add retry to handle_t32_session_open
fn handle_t32_session_open(id: text, body: text) -> text:
    # ... parameter extraction ...
    var attempts = 0
    val max_attempts = 3
    var last_error = ""
    while attempts < max_attempts:
        val result = t32_try_connect(host, port, intercom_name)
        match result:
            Ok(session): return t32_make_session_result(id, session)
            Err(msg):
                last_error = msg
                attempts = attempts + 1
                if attempts < max_attempts:
                    val delay_ms = 500 * (2 ** (attempts - 1))   # 500, 1000, 2000
                    rt_sleep_ms(delay_ms)
    t32_make_tool_error(id, -32602,
        "connection failed after {max_attempts} attempts: {last_error}")

# REQ-F3-001: New handler
fn handle_t32_session_info(id: text, body: text) -> text:
    pass_todo

# REQ-F3-004: New handler
fn handle_t32_status_snapshot(id: text, body: text) -> text:
    pass_todo
```

### window_tools.spl Changes

```simple
# REQ-F2-004: Add mode param to handle_t32_window_capture
fn handle_t32_window_capture(id: text, body: text) -> text:
    val mode = t32_extract_field(body, "mode")
    var capture_mode = "diff"  # default
    if mode == "summary" or mode == "full":
        capture_mode = mode
    # ... existing capture logic ...
    val content = captured_text

    # Snapshot integration
    val prev = T32SnapshotStore.get(session.id, MCP_T32_CURRENT_CORE, window_key)
    val snap = T32SnapshotStore.store(session.id, MCP_T32_CURRENT_CORE,
                                       window_key, window_title, content)
    match capture_mode:
        "full":
            return t32_make_full_capture_result(id, snap)
        "summary":
            if prev.?:
                val (changed, entries) = T32SnapshotStore.diff(prev!, content)
                return t32_make_summary_result(id, snap, changed, entries.len())
            return t32_make_summary_result(id, snap, true, 0)
        _:  # "diff"
            if prev.?:
                val (changed, entries) = T32SnapshotStore.diff(prev!, content)
                if not changed:
                    return t32_make_unchanged_result(id, snap)
                # Token budget check
                val diff_json = t32_format_diff_entries(entries)
                val approx_tokens = diff_json.len() / 4
                if approx_tokens > T32_TOKEN_BUDGET_MAX:
                    return t32_make_full_capture_result(id, snap)
                return t32_make_diff_result(id, snap, entries)
            # First capture — return full
            return t32_make_full_capture_result(id, snap)

# REQ-F5-003: Fix SDN catalog error reporting
fn t32_get_window_catalog() -> [text]:
    val sdn_content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
    var catalog: [text] = []
    if sdn_content != "":
        catalog = t32_parse_window_sdn(sdn_content)
    if t32_text_list_len(catalog) == 0:
        t32_stderr("WARNING: SDN catalog parse returned 0 entries, using fallback")
        catalog = t32_hardcoded_window_catalog()
    catalog
```

### action_tools.spl Changes

```simple
# REQ-F5-001: Replace O(N) field lookup with Dict-style parallel arrays
# (True Dict<text,text> preferred if available; parallel arrays as fallback)
var MCP_T32_FIELD_DICT_KEYS: [text] = []
var MCP_T32_FIELD_DICT_VALS: [text] = []

fn t32_field_state_get(session_id: text, field_key: text) -> text:
    val lookup = session_id + ":" + field_key
    # Binary search or hash-based lookup when Dict is available
    var idx = 0
    for k in MCP_T32_FIELD_DICT_KEYS:
        if k == lookup:
            return MCP_T32_FIELD_DICT_VALS[idx]
        idx = idx + 1
    ""

# REQ-F3-002: New handler
fn handle_t32_action_list(id: text, body: text) -> text:
    val window_filter = t32_extract_field(body, "window")
    val catalog = t32_get_window_catalog()
    var actions_json: [text] = []
    for entry in catalog:
        val (key, title, kind, open_cmd, capture_cmd) = t32_parse_catalog_entry(entry)
        if window_filter != "" and key != window_filter:
            continue
        val action_entries = t32_get_window_actions(key)
        for aentry in action_entries:
            val (akey, alabel, atype, atemplate) = t32_parse_action_entry(aentry)
            var r = t32_LB()
            r = r + t32_jp("key", t32_js(akey))
            r = r + "," + t32_jp("label", t32_js(alabel))
            r = r + "," + t32_jp("type", t32_js(atype))
            r = r + "," + t32_jp("window", t32_js(key))
            r = r + "," + t32_jp("template", t32_js(atemplate))
            r = r + t32_RB()
            actions_json = actions_json + [r]
    val array = t32_SB_L() + actions_json.join(",") + t32_SB_R()
    t32_make_tool_result(id, t32_jo1(t32_jp("actions", array)))
```

### protocol.spl Changes

New tool registrations to add to the tool list:

```simple
# F1: Job tools
t32_tool_entry("t32_job_list", "List all background T32 jobs",
    t32_empty_schema(), ...)
t32_tool_entry("t32_job_get", "Get detailed status of a background job",
    t32_schema_job_id(), ...)
t32_tool_entry("t32_job_cancel", "Cancel a running background job",
    t32_schema_job_id(), ...)
t32_tool_entry("t32_job_result", "Get the result of a completed job",
    t32_schema_job_id(), ...)

# F3: Gap closure tools
t32_tool_entry("t32_session_info", "Get detailed info for a session",
    t32_schema_optional_session_id(), ...)
t32_tool_entry("t32_action_list", "List available actions, optionally filtered by window",
    t32_schema_optional_window(), ...)
t32_tool_entry("t32_status_snapshot", "Get run/stop state and system status",
    t32_schema_optional_session_id(), ...)

# F4: CMM validator
t32_tool_entry("t32_cmm_validate", "Validate CMM source for headless safety",
    t32_schema_cmm_validate(), ...)
```

Dispatcher additions in `dispatch_tool()` (action_tools.spl):

```simple
"t32_job_list": handle_t32_job_list(id, body)
"t32_job_get": handle_t32_job_get(id, body)
"t32_job_cancel": handle_t32_job_cancel(id, body)
"t32_job_result": handle_t32_job_result(id, body)
"t32_session_info": handle_t32_session_info(id, body)
"t32_action_list": handle_t32_action_list(id, body)
"t32_status_snapshot": handle_t32_status_snapshot(id, body)
"t32_cmm_validate": handle_t32_cmm_validate(id, body)
```

### Resource URI Additions

```
t32:///jobs              — list of active jobs
t32:///jobs/<id>         — full job state + result
t32:///windows/<session>/<window> — full snapshot content for a captured window
```

---

## Timeout Defaults

| Context | Parameter | Default (ms) |
|---------|-----------|-------------|
| Session connect | `connect_timeout_ms` | 5000 |
| Quick command/eval | `command_timeout_ms` | 5000 |
| Window capture | `capture_timeout_ms` | 5000 |
| CMM foreground wait | `practice_wait_timeout_ms` | 30000 |
| Background job | `timeout_ms` | 300000 (5 min) |
| Foreground->background escalation | (auto) | 10x foreground timeout |
| Job retention | `T32_JOB_RETENTION_MS` | 300000 (5 min) |
| Snapshot TTL | `T32_SNAPSHOT_TTL_MS` | 300000 (5 min) |

---

## Cross-References

| This Design | References |
|-------------|------------|
| T32Job class | Research: "T32Job class" section (line 382-402) |
| State machine | Research: "Status state machine" section (line 404-430) |
| T32JobManager | Research: "T32JobManager class" section (line 431-581) |
| Snapshot model | Research: "Window snapshot model" section (line 988-1048) |
| Diff strategy | Research: "Diff strategy" section (line 1007-1030) |
| Blocking patterns | Research: "Blocking CMM" section (line 817-861) |
| Timeout policy | Research: "Timeout Policy" section (line 785-815) |
| CLI-MCP mapping | Research: "CLI-to-MCP Tool Mapping" (line 97-170) |
| F1 requirements | REQ-F1-001 through REQ-F1-007 |
| F2 requirements | REQ-F2-001 through REQ-F2-008 |
| F3 requirements | REQ-F3-001 through REQ-F3-004 |
| F4 requirements | REQ-F4-001 through REQ-F4-005 |
| F5 requirements | REQ-F5-001 through REQ-F5-004 |
| Task plan | doc/03_plan/t32_mcp_cli_improvements.md (T1-T36) |
