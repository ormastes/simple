# LLM Diagnostics Library — Requirements

**Date:** 2026-04-06
**Feature:** llm_diagnostics
**Research:** `doc/01_research/local/llm_diagnostics.md`
**Priority:** High (foundation for LLM dashboard)

---

## 1. Overview

A library and hook binary that captures, correlates, and presents LLM session diagnostics — token usage, cache behavior, MCP tool traffic, subagent lifecycle, and inter-agent communication. Initially targets Claude Code; designed for multi-provider expansion (Codex, Gemini).

---

## 2. Functional Requirements

### FR-01: Session Event Capture

| ID | Requirement | Source |
|----|-------------|--------|
| FR-01.1 | Capture SessionStart/SessionEnd events with session_id, timestamp | Hooks |
| FR-01.2 | Capture startup context (cwd, permission_mode, transcript_path) | Hooks |
| FR-01.3 | Detect session type (fresh, resume, clear, compact) | Hooks |

### FR-02: Token Usage Tracking

| ID | Requirement | Source |
|----|-------------|--------|
| FR-02.1 | Track input_tokens, output_tokens per turn | Transcript |
| FR-02.2 | Track cache_read_input_tokens, cache_creation_input_tokens | Transcript |
| FR-02.3 | Compute total_input = input + cache_read + cache_creation | Derived |
| FR-02.4 | Track per-model token breakdown (model_usage) | Transcript |
| FR-02.5 | Estimate startup overhead tokens (first-turn cache_creation) | Derived |
| FR-02.6 | Estimate skill/file content token cost (~4 chars/token) | Heuristic |
| FR-02.7 | Running cumulative token totals per session | Derived |

### FR-03: MCP Tool Tracking

| ID | Requirement | Source |
|----|-------------|--------|
| FR-03.1 | Log every MCP tool call (server, tool, request payload) | Hooks (PreToolUse) |
| FR-03.2 | Log every MCP tool response (payload, latency) | Hooks (PostToolUse) |
| FR-03.3 | Log MCP failures (error, tool_use_id) | Hooks (PostToolUseFailure) |
| FR-03.4 | Track MCP elicitation dialogs | Hooks (Elicitation*) |
| FR-03.5 | Compute per-MCP-server call count, avg latency, total payload size | Derived |
| FR-03.6 | Estimate token cost of MCP request/response content | Heuristic |
| FR-03.7 | Time-based MCP call timeline view | Derived |
| FR-03.8 | MCP server in/out list view (grouped by server) | Derived |

### FR-04: Subagent & Agent Team Tracking

| ID | Requirement | Source |
|----|-------------|--------|
| FR-04.1 | Track SubagentStart (agent_id, agent_type, timestamp) | Hooks |
| FR-04.2 | Track SubagentStop (transcript_path, last_message, duration) | Hooks |
| FR-04.3 | Build agent topology graph (parent → child via parent_tool_use_id) | Transcript |
| FR-04.4 | Per-agent token attribution (from agent transcripts) | Transcript |
| FR-04.5 | Inter-agent message direction (who sent what to whom) | Transcript |
| FR-04.6 | Agent team summary (total agents, total tokens, duration) | Derived |

### FR-05: Content Inspection

| ID | Requirement | Source |
|----|-------------|--------|
| FR-05.1 | Optionally capture tool input/output content | Hooks |
| FR-05.2 | Optionally capture inter-agent message content | Transcript |
| FR-05.3 | File read content tracking (path, size, estimated tokens) | Hooks (PostToolUse for Read) |
| FR-05.4 | Skill load detection and content size | SessionStart context |
| FR-05.5 | Content truncation/summarization for large payloads | Config |

### FR-06: Cache Analysis

| ID | Requirement | Source |
|----|-------------|--------|
| FR-06.1 | Per-turn cache hit/miss/write status | Transcript |
| FR-06.2 | Cache efficiency ratio (cache_read / total_input) | Derived |
| FR-06.3 | Cache cost savings estimate (read tokens at reduced price) | Derived |
| FR-06.4 | Identify which content is likely cached vs uncached | Heuristic |

### FR-07: Task/Todo Integration

| ID | Requirement | Source |
|----|-------------|--------|
| FR-07.1 | Track TaskCreate/TaskCompleted events | Hooks |
| FR-07.2 | Associate token cost with task boundaries | Correlation |
| FR-07.3 | Task progress timeline view | Derived |

### FR-08: Time-Based Views

| ID | Requirement | Source |
|----|-------------|--------|
| FR-08.1 | Chronological event timeline (all event types) | All sources |
| FR-08.2 | Time-windowed aggregation (per-minute, per-turn) | Derived |
| FR-08.3 | LLM message view (user prompts, assistant responses, timestamps) | Transcript |
| FR-08.4 | MCP call timeline (start/end, latency bars) | Hooks |

### FR-09: Hook Event Management

| ID | Requirement | Source |
|----|-------------|--------|
| FR-09.1 | Show/hide hook events by type (filter) | UI config |
| FR-09.2 | Hook event detail expand/collapse | UI |
| FR-09.3 | Hook registration helper (generate settings.json config) | CLI tool |

---

## 3. Non-Functional Requirements

| ID | Requirement |
|----|-------------|
| NFR-01 | Hook handler must complete in <50ms (Claude Code blocks on hooks) |
| NFR-02 | JSONL log file format for append-only durability |
| NFR-03 | Session correlation via session_id across all event types |
| NFR-04 | Multi-provider design (Claude now; Codex, Gemini later) |
| NFR-05 | Content capture opt-in (privacy: off by default for payloads) |
| NFR-06 | Max log file size configurable with rotation |
| NFR-07 | Library usable standalone (no dashboard dependency) |
| NFR-08 | Dashboard integration via WebSocket export |

---

## 4. Architecture Decision

**Recommended: Option B (Hook + Transcript Parser)**

Rationale:
- Hooks give real-time MCP/subagent/session events
- Transcript JSONL gives token usage, cache metrics, message content
- Correlation via session_id bridges both sources
- No external SDK dependency; works with stock Claude Code
- Extensible to Option C (SDK/OTel) later

---

## 5. Component Breakdown

### 5.1 Library (`src/lib/nogc_async_mut/llm_diagnostics/`)

| Component | Responsibility |
|-----------|---------------|
| `types.spl` | Event types, token metrics, agent graph nodes |
| `collector.spl` | Event buffer, session state, correlation engine |
| `hook_handler.spl` | Parse hook JSON stdin, emit typed events |
| `transcript_parser.spl` | Read JSONL transcripts, extract usage/messages |
| `token_estimator.spl` | Content → token heuristic (~4 chars/token, configurable) |
| `cache_analyzer.spl` | Cache hit/miss/efficiency computations |
| `agent_graph.spl` | Build parent→child agent tree, token attribution |
| `mcp_tracker.spl` | Per-server/tool call stats, latency, payload tracking |
| `timeline.spl` | Merge all events into time-ordered stream |
| `formatters/*` | JSON, text table, HTML fragment output |
| `exporters/*` | File (JSONL), WebSocket (dashboard) |

### 5.2 Hook Binary (`src/app/llm_diag_hook/`)

- Reads JSON from stdin
- Routes to appropriate handler by event type
- Appends to session JSONL log
- Exits 0 (never blocks Claude Code)
- Target: <50ms total execution

### 5.3 Dashboard Integration

- Extend `src/app/llm_dashboard/` with diagnostics panels
- WebSocket channel for live event stream
- Phase 2 work (after library is stable)

---

## 6. Provider Expansion Plan

| Provider | Phase | Data Sources |
|----------|-------|-------------|
| Claude Code | 1 (now) | Hooks + Transcripts |
| Codex CLI | 2 | Log files + API usage |
| Gemini CLI | 2 | Extension events + API usage |
| Agent SDK (any) | 3 | Stream events + OTel |

---

## 7. Acceptance Criteria

1. Hook binary installs and captures all listed event types
2. Library parses transcripts and extracts token/cache metrics
3. Agent graph correctly traces parent→child relationships
4. MCP tracker shows per-server/tool call stats
5. Timeline merges hooks + transcript data chronologically
6. JSON formatter outputs valid, machine-readable diagnostics
7. Text formatter outputs human-readable terminal tables
8. All operations meet <50ms hook latency requirement
9. Content capture is opt-in and off by default
10. Tests cover all event types with mock data
