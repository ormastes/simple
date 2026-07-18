# LLM Caret Claude CLI Full Parity - Production Implementation Plan

Date: 2026-07-05
Updated: 2026-07-07 (replaced matrix/size-parity plan with phased production plan)

## Reset (2026-07-07)

The prior plan pursued file/LOC/symbol matrix completion with a strict
size-parity gate (target LOC >= source LOC). Audit shows this drove ~1,290
`parity-ledger` comment-padding lines and a disconnected ~151K-LOC
`claude_full/` island that never wired into the shipped CLI. **That plan is
retired.** Size parity is not a goal; LOC is not evidence. Parity is measured by
executed behavior in the **shipped path** (`src/app/llm_caret/*.spl`, ~3,086
LOC), with `claude_full/` treated as a parts bin.

Design reference: `doc/05_design/llm_caret_claude_cli_full_parity.md`
(current-state + per-dimension design and claude_full dispositions).

## Quality Gate (applies to every task)

- Interpreter-mode "PASS" is **insufficient**. `.claude/rules/testing.md` notes
  the interpreter test runner may verify file loading only, NOT `it`-block
  execution. Every acceptance test below must be run in a mode that executes
  `it` blocks, and the true pass/fail (assertion-level) recorded. A task is not
  done on a file-load PASS.
- Acceptance asserts on **behavior**, not struct fields — e.g. a spawn spy for
  permission deny, an attempt counter for retry, a transcript scan for redaction.
- All FS/process/network via owner facades (MDSOC+); no raw runtime shortcuts.

---

## Phase 0 — Truth Reset

- **0.1 Mark overclaims.** Update the design/plan/harden docs (this set) and add
  a note to `doc/09_report/llm_caret_claude_cli_traceability.md` that "full
  parity / 0 stubs" was never achieved and the size-parity gate is retired.
  - Files: this doc + the three sibling docs (already updated 2026-07-07).
  - Exit: no doc claims claude_full is wired or that 0 stubs exist.
- **0.2 Remove the size-parity gate.** Delete the size-parity checker
  invocation and the `target_min_loc` completion condition from tooling/CI.
  - Files: `scripts/check/check-llm-caret-claude-cli-trace.shs` (drop LOC>=source
    gate; keep as docs-coverage only), any CI wiring.
  - Acceptance: checker no longer fails on LOC; parity-ledger padding is no
    longer required by any gate.
  - Exit: no gate rewards LOC.
- **0.3 Per-module island decision.** For each `claude_full/` subtree, record
  WIRE-IN / REWRITE / DELETE per the design doc dispositions (compact + session
  history -> wire; tools/* stubs + FileReadTool -> rewrite; mcp UI, workSecret,
  agents editors, parity-ledger padding -> delete or ignore).
  - Files: a disposition table appended to this plan or a new
    `doc/03_plan/trace/llm_caret_claude_full_disposition.tsv`.
  - Exit: every claude_full top-level dir has a recorded disposition.

## Phase 1 — P0s (safety and reliability of the shipped path)

**Status (2026-07-07): DONE.** 1.1 `tools.spl` (28/28), 1.2 `retry.spl` (29/29),
1.3 `redact.spl` (20/20). Plus a JSON response-parsing correctness fix
(`json_find`/`_digit_val` in `json_helpers.spl`) that root-caused a cross-module
`char.to_i64`/`Option<i64>` tag-box miscompilation — all 9 shipped modules
rewired; full llm_caret unit suite 273 pass / 0 fail. Landed at origin
`d90b9c3f`. See bug `llm_caret_index_of_optioni64_tagbox_2026-07-07`.

- **1.1 Real tool execution + permission gating.**  ✅ DONE
  - Scope: `run_tool(name,input)` dispatch + single `permission_gate` all calls
    traverse; real executors (process spawn, FS read/write/edit, WebFetch).
  - Files: new dispatch/gate module under `src/app/llm_caret/`; rewrite/port from
    `claude_full/tools/*` and `bridge/bridgePermissionCallbacks.spl` structs;
    wire into `provider.spl`.
  - Acceptance (it-block): denied Bash does NOT spawn (spawn spy); allowed does;
    `ask` routes to responder; no tool executes ungated.
  - Exit: every tool path is gated and really executes.
- **1.2 Retry/backoff/timeout.**  ✅ DONE
  - Scope: `with_retry` around `dispatch_send`; per-attempt timeout on every
    `rt_http_request`/`rt_process_run`; retryable-vs-terminal error type.
  - Files: `provider.spl`, `claude_api.spl`, `claude_cli.spl`, `openai_api.spl`.
  - Acceptance (it-block): 429-then-200 succeeds after backoff (assert attempts);
    persistent-500 exhausts and returns terminal error; hung subprocess killed at
    timeout.
  - Exit: no transient failure surfaces raw; no unbounded subprocess wait.
- **1.3 Secret redaction + injection defense.**  ✅ DONE
  - Scope: redaction pass before any log/JSONL persist; tag/wrap untrusted tool
    output before it re-enters history.
  - Files: `provider.spl`, `chat.spl`, WebFetch/file-read executors.
  - Acceptance (it-block): persisted transcript has no raw API key; WebFetch
    output is wrapped/tagged in history.
  - Exit: no secret in transcripts/logs; untrusted output is fenced.

## Phase 2 — P1s (capability parity)

- **2.1 MCP client.** stdio transport, `.mcp.json` load, initialize/list/call;
  discovered tools register into 1.1's dispatch and pass the gate.
  - Files: new `mcp_client.spl` (+ transport); ignore `claude_full` mcp UI.
  - Acceptance: fake-transport it-block handshake->list->call invokes a discovered
    tool through the gate; one opt-in credential-gated live system test.
  - Exit: an external MCP server's tools are usable.
- **2.2 Prompt-cache breakpoints.** Insert `cache_control` on system prompt +
  static tool block in `build_claude_api_body` (`claude_api.spl`).
  - Acceptance: it-block asserts breakpoint markers in built JSON body.
  - Exit: multi-turn reuses cached prefixes.
- **2.3 Summarizing compaction + resume.** Summarize oldest span in `chat.spl`;
  persist history JSONL per turn; `--resume <id>` load in `claude_cli.spl`.
  - Files: `chat.spl`, `claude_cli.spl`, `provider.spl`; wire compact model/paging
    from `claude_full/commands/compact/compact.spl` +
    `assistant/sessionHistory.spl`.
  - Acceptance: it-block: >budget history compacted to summary+tail (summary call
    issued); `--resume` reconstructs history.
  - Exit: truncation is no longer the only strategy; sessions resume.
- **2.4 Crash resume.** Per-turn JSONL persist (shared with 2.3) + top-level
  error boundary + recovery marker.
  - Acceptance: it-block simulates mid-turn kill; `--resume` recovers completed
    turns.
  - Exit: a crash loses at most the in-flight turn.
- **2.5 Subagent runtime.** Minimal single `Task` spawn+return with own history
  and gated tool subset.
  - Files: new `task_runtime.spl`.
  - Acceptance: it-block spawns one subagent running a gated tool; parent history
    holds the synthesized result. If deferred, DESCOPE explicitly in docs.
  - Exit: single-subagent loop works, or subagents are documented out of scope.
- **2.6 Chat UI on Simple TUI (pure-Simple).**  [added 2026-07-07, user directive]
  - Scope: interactive chat shell built on `std.tui` (pure-Simple, ANSI, no
    ncurses/FFI): `BoxWidget` transcript, `ListWidget` scrollback, `InputWidget`
    prompt, `style.*` user-vs-assistant. Replace the raw `print` at `chat.spl:172`
    (`_emit_tool`) with a `render_tool_call` widget line via a renderer seam on
    `run_agent_loop`. Default to TUI on an interactive tty; fall back to plain
    `print` when non-tty (piped/CI/server) — "Simple TUI in most cases".
  - Files: new `src/app/llm_caret/chat_tui.spl`; edit `chat.spl` (renderer seam),
    `mod.spl` (exports); pattern from `src/app/editor/tui_shell.spl`.
  - Acceptance (it-block): pure formatting helpers produce expected turn/tool-line
    strings and distinct user/assistant styling; renderer seam selects TUI vs
    plain by tty/flag; a fake-model loop iteration calls `render_tool_call` (not
    `print`) in TUI mode.
  - Exit: interactive `llm_caret` chats through a `std.tui` UI; headless/JSON
    paths unchanged. Streaming token re-render is a documented upgrade path.

## Phase 3 — P2s + observability + live gates

- **3.1 Streaming buffer-boundary robustness.** `claude_cli.spl` reassembles a
  JSON event split across process-output chunks.
  - Acceptance: it-block feeds a split `CliStreamEvent` line, asserts one event.
- **3.2 Observability.** Structured JSON-lines events around `dispatch_send`
  (latency, error class, retry decisions, token/cost); `/cost`-style surface.
  - Acceptance: it-block asserts one dispatch emits the event with all fields.
  - Exit: NFR-LLM-CARET-FULL-004 met.
- **3.3 Live-test gates.** Convert the opt-in live specs
  (`test/03_system/tools/llm/llm_caret_live_spec.spl`,
  `llm_caret_live_comprehensive_spec.spl`) to run their `it` blocks in a real
  execution mode in CI (credential-gated), and record true pass/fail. Audit
  thin specs (`opencode_cli_spec.spl`, 43 LOC) against their implementation.
  - Exit: recorded assertion-level pass counts, not file-load PASS.

## Completion Criteria

Parity is done when every Phase 1-3 acceptance it-block passes in an
`it`-executing mode, `claude_full/` disposition is fully resolved (wired or
deleted, no unreferenced island claimed as parity), and no doc or gate cites LOC
or symbol-name presence as evidence of behavior.
