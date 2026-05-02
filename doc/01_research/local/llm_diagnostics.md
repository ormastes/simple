# LLM Diagnostics Library — Local Research

**Date:** 2026-04-06
**Feature:** LLM Diagnostics / Observability Library
**Status:** Research Complete

---

## 1. Existing Infrastructure

### 1.1 LLM Module (`src/lib/nogc_async_mut/llm/`)

Already tracks per-response tokens:
- `ChatResponse` has `input_tokens: i64`, `output_tokens: i64`
- `StreamEvent` carries delta token counts
- Provider abstraction: claude_api, openai, gemini_api, local_torch, claude_cli, openai_compat
- No cache token breakdown (cache_read, cache_creation) yet
- No cost calculation module

### 1.2 Dashboard (`src/app/llm_dashboard/`, `src/app/web_dashboard/`)

- `AgentDashboardStore` watches `~/.claude/projects/` for JSONL transcripts
- TUI mode (default) + Web GUI mode (HTTP + WebSocket on port 3001)
- Routes: `/api/tmux/*`, `/ws/terminal`, `/ws/agents`
- Existing collectors in `dashboard_collectors.spl`

### 1.3 MCP SDK (`src/lib/nogc_sync_mut/mcp_sdk/`)

- Full JSON-RPC transport, tool dispatch, resource/prompt definitions
- Used by 4 MCP servers (simple-mcp, simple-lsp-mcp, t32-mcp, t32-lsp-mcp)

### 1.4 Diagnostics (`src/lib/common/diagnostics/`)

- Platform-agnostic formatters (JSON, Text)
- i18n context support
- Compiler-level diagnostics with severity, labels, spans

### 1.5 Debug Hooks (`src/app/dap/hooks.spl`)

- Interpreter hook context for DAP debugging
- 17+ extern `rt_hook_*` functions
- Pattern: hook registration → event capture → state inspection

---

## 2. Claude Code Hook Events (Data Sources)

### 2.1 Available Hook Events

| Event | Fields | Captures |
|-------|--------|----------|
| **PreToolUse** | tool_name, tool_input, tool_use_id, session_id, transcript_path | MCP/tool requests before execution |
| **PostToolUse** | tool_name, tool_input, tool_response, tool_use_id | MCP/tool responses after execution |
| **PostToolUseFailure** | tool_name, tool_input, tool_use_id, error | Failed tool calls |
| **SessionStart** | session_id, transcript_path, cwd, permission_mode | Startup detection |
| **SessionEnd** | session_id | Session close |
| **SubagentStart** | agent_id, agent_type | Subagent spawn |
| **SubagentStop** | agent_id, agent_type, transcript_path, last_message | Subagent complete |
| **Elicitation** | mcp_server_name, message, mode, url, elicitation_id | MCP user-input request |
| **ElicitationResult** | mcp_server_name, action, content, mode, elicitation_id | MCP user-input response |
| **PermissionRequest** | tool_name, tool_input, permission_suggestions | Permission dialog |
| **PermissionDenied** | tool_name, tool_input | Blocked tool call |
| **UserPromptSubmit** | — | User message sent |
| **PreCompact** | — | Context compaction |
| **Notification** | — | System notification |
| **Stop** | — | Generation stopped |
| **TaskCompleted** | — | Task finished |
| **TeammateIdle** | — | Team agent idle |
| **ConfigChange** | — | Settings changed |

### 2.2 Hook Configuration

```json
{
  "hooks": {
    "PreToolUse": [{
      "matcher": "mcp__.*|Bash|Read|Agent|Task.*",
      "hooks": [{ "type": "command", "command": "bin/llm_diag_hook" }]
    }],
    "PostToolUse": [{
      "matcher": "mcp__.*|Bash|Read|Agent|Task.*",
      "hooks": [{ "type": "command", "command": "bin/llm_diag_hook" }]
    }],
    "SessionStart": [{
      "hooks": [{ "type": "command", "command": "bin/llm_diag_hook --event session_start" }]
    }],
    "SubagentStart": [{
      "hooks": [{ "type": "command", "command": "bin/llm_diag_hook --event subagent_start" }]
    }],
    "SubagentStop": [{
      "hooks": [{ "type": "command", "command": "bin/llm_diag_hook --event subagent_stop" }]
    }]
  }
}
```

### 2.3 Hook Input/Output Protocol

- **Command hooks:** JSON via stdin, exit 0=ok, 2=block
- **HTTP hooks:** POST JSON body, response controls behavior
- **Stdout:** Can return `{ "decision": "allow"|"block"|"modify", "reason": "..." }`

---

## 3. Agent SDK Token Fields

### 3.1 Usage Object (per-message)

```json
{
  "input_tokens": 1500,
  "output_tokens": 300,
  "cache_read_input_tokens": 800,
  "cache_creation_input_tokens": 200
}
```

**Total input:** `input_tokens + cache_read_input_tokens + cache_creation_input_tokens`

### 3.2 Model Usage (per-result)

```json
{
  "model_usage": {
    "claude-opus-4-6": { "input_tokens": 5000, "output_tokens": 1200 },
    "claude-haiku-4-5-20251001": { "input_tokens": 800, "output_tokens": 200 }
  }
}
```

### 3.3 Subagent Linkage

- `parent_tool_use_id` in transcript messages links child → parent
- Subagent `session_meta.parentToolCallId` for distributed tracing

---

## 4. Data Availability Matrix

| Feature | Hooks | SDK/API | Transcript | Estimable |
|---------|-------|---------|------------|-----------|
| MCP tool called | ✅ PreToolUse | — | ✅ | — |
| MCP request payload | ✅ tool_input | — | ✅ | — |
| MCP response payload | ✅ PostToolUse | — | ✅ | — |
| MCP failure/error | ✅ PostToolUseFailure | — | ✅ | — |
| Input tokens | — | ✅ usage | ✅ | — |
| Output tokens | — | ✅ usage | ✅ | — |
| Cache read tokens | — | ✅ usage | ✅ | — |
| Cache creation tokens | — | ✅ usage | ✅ | — |
| Startup token overhead | ✅ SessionStart | — | — | ✅ |
| Skill load tokens | — | — | — | ✅ (content size) |
| File read tokens | ✅ PostToolUse(Read) | — | ✅ | ✅ (content length) |
| Subagent lifecycle | ✅ SubagentStart/Stop | — | ✅ | — |
| Inter-agent messages | — | ✅ parent_tool_use_id | ✅ | — |
| Agent-level token breakdown | — | ✅ model_usage | ✅ | — |
| Per-model cost | — | ✅ model_usage | — | ✅ (pricing table) |
| Permission events | ✅ PermissionRequest/Denied | — | — | — |
| Context compaction | ✅ PreCompact | — | — | — |
| User prompt timing | ✅ UserPromptSubmit | — | ✅ | — |

---

## 5. Gaps & Limitations

### 5.1 Not Available Natively

1. **Startup token decomposition** — no field for "X tokens from CLAUDE.md, Y from MCP introductions, Z from skills"
2. **Per-agent cache attribution** — cannot say "subagent A's cache hit was N tokens"
3. **Skill load token cost** — hooks don't fire when skills are expanded; only estimable from content size
4. **Hook event token cost** — hooks themselves don't carry token counts
5. **Context window composition** — no breakdown of system prompt vs user content vs tool definitions

### 5.2 Workarounds

1. **Startup overhead:** Estimate via first-turn `cache_creation_input_tokens` (system context gets cached)
2. **Skill token cost:** Measure skill file sizes, apply ~4 chars/token heuristic
3. **Per-agent attribution:** Correlate SubagentStart/Stop timestamps with transcript usage entries
4. **MCP intro tokens:** Compare first-turn input_tokens with/without MCP servers enabled
5. **Context composition:** Parse transcript JSONL, sum content lengths by role/type

---

## 6. Architecture Options

### Option A: Hook-Only Logger (Simplest)

- Install command hooks for all events
- Log to JSONL file per session
- Post-hoc analysis with dashboard
- **Pro:** No SDK dependency, works with any Claude Code version
- **Con:** No real-time token counts, no cache breakdown

### Option B: Hook + Transcript Parser (Recommended)

- Hooks for real-time event capture (tool calls, subagent lifecycle)
- Transcript JSONL parser for token usage, cache metrics, message content
- Combine via session_id correlation
- **Pro:** Rich data, cache visibility, inter-agent tracing
- **Con:** Slight latency for transcript parsing, file watching needed

### Option C: Hook + SDK Integration (Full)

- All of Option B, plus
- Agent SDK stream events for live token updates
- OTel exporter for external dashboards (Grafana, etc.)
- **Pro:** Maximum observability, real-time, external integrations
- **Con:** SDK dependency, more complex setup

---

## 7. Proposed Module Structure

```
src/lib/nogc_async_mut/llm_diagnostics/
├── mod.spl                    # Public API
├── types.spl                  # Event types, token metrics, agent graph
├── collector.spl              # Event buffering, session correlation
├── hook_handler.spl           # Claude Code hook JSON parser
├── transcript_parser.spl      # JSONL transcript reader
├── token_estimator.spl        # Heuristic token counting (content → tokens)
├── cache_analyzer.spl         # Cache hit/miss analysis
├── agent_graph.spl            # Agent team topology, message flow
├── mcp_tracker.spl            # MCP tool call/response tracking
├── timeline.spl               # Time-ordered event stream
├── formatters/
│   ├── __init__.spl
│   ├── json_formatter.spl     # JSON output
│   ├── text_formatter.spl     # Terminal table output
│   └── html_formatter.spl     # Dashboard HTML fragments
└── exporters/
    ├── __init__.spl
    ├── file_exporter.spl      # JSONL file writer
    └── ws_exporter.spl        # WebSocket live stream
```

**Hook binary:** `src/app/llm_diag_hook/main.spl` → `bin/llm_diag_hook`
**Dashboard integration:** Extend `src/app/llm_dashboard/` with diagnostics views

---

## 8. Related Prior Work

- `src/lib/common/diagnostics/` — formatter patterns reusable
- `src/app/dap/hooks.spl` — hook registration pattern
- `src/app/llm_dashboard/` — transcript watching, agent store
- `src/lib/nogc_async_mut/llm/types.spl` — token field conventions
- `src/lib/nogc_sync_mut/mcp_sdk/` — JSON-RPC parsing patterns
