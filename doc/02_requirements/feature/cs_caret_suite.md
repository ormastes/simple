# Feature: `cs` — Caret Suite

Status: in development (2026-09-03)

`cs` is the caret suite entry point: one command that launches, runs and manages
multiple LLM agents through the agent manager, with a dashboard that shows
overall status and the detail of the selected agent.

## FR-1 — `cs` with no arguments shows the dashboard

Running `cs` (or `simple cs`) opens a dashboard, not a one-shot dump. It shows:

- a status header: whether the agent manager is connected, agent count, states;
- an agent list, one entry selectable;
- detail for the selected agent;
- a chat/command input field pinned to the **bottom** of the view.

`cs <session>` targets a named session; the default session is `caret`.

## FR-2 — Launch spec grammar: `harness[:provider][/model]`

One short form chooses a harness with its default model, or names both.

| form | meaning |
|---|---|
| `claude` | claude CLI harness, its default model |
| `claude/opus` | claude CLI harness, model `opus` |
| `codex`, `kimi`, `opencode`, `gemini` | that CLI harness, default model |
| `caret:kimi` | caret's own TUI backed by the kimi provider |
| `caret:glm/glm-4.6` | caret backed by glm, model `glm-4.6` |
| `caret:slang/deepseek-v3` | caret backed by the local slang runtime serving deepseek-v3 |
| `caret:deepseek` | caret backed by the deepseek provider |

Only `caret` takes a `:provider`; a CLI harness given one is rejected with a
specific error. An unparseable spec surfaces the parser's own error text and
launches nothing.

## FR-3 — Pane control

- switch the pane of an agent (`/switch`);
- maximize the pane currently taking a command (`/max`).

## FR-4 — Multi-agent management

`cs` launches several agents, tracks them through the agent manager, reports
per-agent status/pid/CPU/RSS, and stops them on request.

## FR-5 — Command set (short by design)

`/launch <spec>` · `/switch <n|id>` · `/max` · `/kill <n|id>` · `/agents` ·
`/help` · `/quit`. Bare text is a chat message to the selected agent; with no
selection it returns a clear error rather than being silently dropped.

## FR-6 — Providers

`caret:deepseek` resolves through the existing OpenAI-compatible client.
`caret:slang/<model>` resolves against the in-repo slang runtime's
OpenAI-compatible HTTP surface (phase A6 of the slang master plan).

## FR-7 — Windows

`cs` runs on Windows. `bin/cs.cmd` delegates to `bin\simple.cmd cs` so binary
resolution is not duplicated. tmux does not exist on Windows, so the pane
backend degrades to what the host can honestly provide; it never fabricates a
pane list.

## Non-goals

Streaming completions from the slang server. Reimplementing a TUI framework —
`cs` reuses the existing `chat_tui` widgets. Replacing tmux as the POSIX pane
backend.

## Honesty constraints (these are requirements, not style)

- No fabricated agent state. A pid that is gone, a manager that is unreachable,
  or a usage sample that could not be taken must be reported as such — never as
  a plausible zero. `sosix_proc_usage` returns `valid: false` for this reason.
- The slang path must not return canned text presented as inference. If the
  model cannot run, the response is a structured error naming the reason.
- A pane operation that cannot be performed reports failure with a reason.

## Traceability

Design: `doc/05_design/app/llm_caret/cs_caret_suite.md`
Guide: `doc/07_guide/app/llm_caret_usage.md`
