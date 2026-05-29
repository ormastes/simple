# LLM Diagnostics Library — Detail Design

**Date:** 2026-04-06
**Research:** `doc/01_research/local/llm_diagnostics.md`
**Requirements:** `doc/02_requirements/feature/llm_diagnostics.md`

---

## 1. Module Layout

```
src/lib/nogc_async_mut/llm_diagnostics/
├── mod.spl                  # Public API + module state
├── types.spl                # All struct/enum definitions
├── collector.spl            # Event buffer + session correlation
├── hook_handler.spl         # JSON stdin parser for Claude Code hooks
├── transcript_parser.spl    # JSONL transcript file reader
├── token_estimator.spl      # Content → token heuristic
├── cache_analyzer.spl       # Cache hit/miss/efficiency
├── agent_graph.spl          # Agent tree + message flow
├── mcp_tracker.spl          # MCP tool call stats
├── timeline.spl             # Time-ordered event merge
├── formatters/
│   ├── __init__.spl
│   ├── json_formatter.spl   # JSON output
│   └── text_formatter.spl   # Terminal table output
└── exporters/
    ├── __init__.spl
    ├── file_exporter.spl    # JSONL append
    └── ws_exporter.spl      # WebSocket live stream

src/app/llm_diag_hook/
├── main.spl                 # Hook binary entry point
```

---

## 2. Core Types (`types.spl`)

### 2.1 Event Types

```simple
struct DiagEvent:
    event_type: text        # "session_start", "tool_pre", "tool_post", etc.
    timestamp: i64          # Unix millis
    session_id: text
    agent_id: text          # "" for main agent
    parent_agent_id: text   # "" for root
    data: text              # JSON payload (event-specific)

struct TokenUsage:
    input_tokens: i64
    output_tokens: i64
    cache_read_input_tokens: i64
    cache_creation_input_tokens: i64

struct ToolCall:
    tool_use_id: text
    tool_name: text
    server_name: text       # extracted from mcp__<server>__<tool>
    request_payload: text   # tool_input JSON
    response_payload: text  # tool_response (post only)
    error: text             # (failure only)
    start_time: i64
    end_time: i64
    estimated_tokens: i64   # heuristic

struct AgentNode:
    agent_id: text
    agent_type: text
    parent_tool_use_id: text
    transcript_path: text
    start_time: i64
    end_time: i64
    total_usage: TokenUsage
    children: [text]        # child agent_ids

struct McpServerStats:
    server_name: text
    call_count: i64
    total_request_bytes: i64
    total_response_bytes: i64
    total_latency_ms: i64
    estimated_request_tokens: i64
    estimated_response_tokens: i64
    calls: [ToolCall]

struct SessionDiag:
    session_id: text
    session_type: text      # "fresh", "resume", "clear", "compact"
    start_time: i64
    events: [DiagEvent]
    total_usage: TokenUsage
    mcp_stats: [McpServerStats]
    agent_tree: [AgentNode]
    turn_count: i64

struct CacheAnalysis:
    total_cache_reads: i64
    total_cache_writes: i64
    total_uncached: i64
    cache_efficiency: f64   # cache_read / total_input
    per_turn: [TurnCache]

struct TurnCache:
    turn_index: i64
    cache_read: i64
    cache_write: i64
    uncached: i64
    was_hit: bool

struct DiagConfig:
    capture_content: bool   # false by default (privacy)
    max_payload_size: i64   # truncate at 4096 chars
    log_path: text          # JSONL output path
    enable_ws: bool         # WebSocket export
    ws_port: i64
    token_ratio: f64        # chars per token (default 4.0)
```

---

## 3. Collector (`collector.spl`)

Module-level state:
```
var DIAG_INITIALIZED: bool = false
var DIAG_CONFIG: DiagConfig
var DIAG_SESSION: SessionDiag
var DIAG_PENDING_TOOLS: Dict<text, ToolCall>  # tool_use_id → in-flight
var DIAG_MCP_STATS: Dict<text, McpServerStats>  # server_name → stats
var DIAG_AGENTS: Dict<text, AgentNode>  # agent_id → node
```

Key functions:
- `diag_init(config: DiagConfig)` — initialize module state
- `diag_push_event(event: DiagEvent)` — buffer + route event
- `diag_get_session() -> SessionDiag` — snapshot current session
- `diag_get_mcp_stats() -> [McpServerStats]` — per-server stats
- `diag_get_agent_tree() -> [AgentNode]` — agent topology
- `diag_get_timeline() -> [DiagEvent]` — chronological events
- `diag_reset()` — clear session state

---

## 4. Hook Handler (`hook_handler.spl`)

Parses JSON from stdin (Claude Code hook protocol):
```
fn handle_hook_stdin() -> DiagEvent:
    val json = read_all_stdin()
    val event_type = extract_json_string(json, "hook_event_name")
    match event_type:
        "PreToolUse": parse_pre_tool_use(json)
        "PostToolUse": parse_post_tool_use(json)
        "PostToolUseFailure": parse_post_tool_use_failure(json)
        "SessionStart": parse_session_start(json)
        "SubagentStart": parse_subagent_start(json)
        "SubagentStop": parse_subagent_stop(json)
        _: parse_generic_event(json, event_type)
```

Each parser extracts fields using `extract_json_string`/`extract_json_int` pattern.

---

## 5. MCP Tool Name Parsing

Extract server/tool from `mcp__<server>__<tool>` format:
```
fn parse_mcp_tool_name(name: text) -> (text, text):
    if not name.starts_with("mcp__"): return ("", name)
    val rest = name.slice(5)  # after "mcp__"
    val sep = rest.index_of("__")
    match sep:
        Some(i): (rest.slice(0, i), rest.slice(i + 2))
        nil: ("", name)
```

---

## 6. Token Estimator (`token_estimator.spl`)

```
fn estimate_tokens(content: text, ratio: f64) -> i64:
    if content.len() == 0: return 0
    val chars = content.len() as f64
    (chars / ratio + 0.5) as i64  # round

fn estimate_tokens_default(content: text) -> i64:
    estimate_tokens(content, 4.0)
```

---

## 7. Cache Analyzer (`cache_analyzer.spl`)

Input: list of per-turn TokenUsage
Output: CacheAnalysis with efficiency metrics

```
fn analyze_cache(turns: [TokenUsage]) -> CacheAnalysis:
    # Sum across turns, compute ratios
```

---

## 8. Agent Graph (`agent_graph.spl`)

Build tree from SubagentStart/Stop events + parent_tool_use_id:
```
fn build_agent_tree(agents: Dict<text, AgentNode>) -> [AgentNode]:
    # Root = agents with parent_tool_use_id == ""
    # Children linked via parent_tool_use_id matching
```

---

## 9. Timeline (`timeline.spl`)

Merge events from hooks + transcript into chronological order:
```
fn build_timeline(events: [DiagEvent]) -> [DiagEvent]:
    # Sort by timestamp
    events.sort_by(\a, b: a.timestamp - b.timestamp)
```

---

## 10. Formatters

### JSON Formatter
Uses existing jp/js/jo/ja patterns from mcp_sdk:
```
fn format_session_json(session: SessionDiag) -> text:
    # Build full JSON report
```

### Text Formatter
Terminal tables with fixed-width columns:
```
fn format_session_text(session: SessionDiag) -> text:
    # Header + rows for token summary, MCP stats, agent tree
```

---

## 11. Hook Binary (`src/app/llm_diag_hook/main.spl`)

Fast entry point (<50ms):
1. Read JSON from stdin
2. Parse event type
3. Append to JSONL log file
4. Exit 0

No heavy processing — analysis happens in library/dashboard.

---

## 12. Dashboard Integration (Phase 2)

Extend `src/app/llm_dashboard/` with:
- Token usage panel (per-turn, cumulative)
- MCP traffic panel (in/out, latency)
- Agent tree panel (topology, per-agent tokens)
- Cache analysis panel (hit/miss ratio)
- Timeline view (all events)

Data flow: hook binary → JSONL → dashboard reads → WebSocket → TUI/Web
