# MCP interpreter-mode startup takes ~11-13s before `initialize` answers
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status
OPEN — breakdown below, fix identified but not yet applied (see "Why not
applied here").

## Symptom
`bin/simple_mcp_server.cmd` (source path — no admitted native
`simple_mcp_server.exe`, so it falls back to
`"%SIMPLE_RUNTIME%" run src\app\mcp\main.spl`, with
`SIMPLE_EXECUTION_MODE=interpreter` forced by the wrapper) takes on the order
of 11-13s of wall time before it answers the first `initialize` request. A
client (Claude Code, Codex) waiting on that response sees a multi-second stall
on every fresh MCP session.

## Measurement

Host: shared Windows box, `bin/release/x86_64-pc-windows-msvc/simple.exe`
(Rust seed), many concurrent `simple.exe` processes observed from other agent
sessions during measurement — absolute numbers below carry real host-load
noise (git commands on this same box routinely took 30-180s during this
investigation); treat them as an order-of-magnitude breakdown, not a tight
benchmark. Runs use `--probe` (exercises every module-level import that
`initialize`/`tools/list` also force, then exits immediately after printing a
one-line summary — cheaper to measure than driving the full JSON-RPC
handshake over stdin).

```
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_LOG=error RUST_LOG=error \
  bin/release/x86_64-pc-windows-msvc/simple.exe run /tmp/trivial.spl        # baseline, no MCP imports
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_LOG=error RUST_LOG=error SIMPLE_MCP_TOOL_SET=all \
  bin/release/x86_64-pc-windows-msvc/simple.exe run src/app/mcp/main.spl --probe
```

| run | elapsed |
|---|---|
| trivial `fn main(): print "hi"` (no imports) | 3.51s, 3.75s |
| `main.spl --probe` (full MCP module graph) | 11.45s, 13.30s |
| `main.spl` driven over stdin with a real `initialize` message, exit on EOF | 5.02s (measured earlier, lower-load moment) |

Interpretation: ~3.5-3.8s is the **fixed interpreter startup cost**, unrelated
to MCP (same order of magnitude as the ~12s fixed lint startup cost recorded
in `.claude/rules/commands.md`). MCP's own module graph adds roughly
**7-10s more** on top of that baseline — this is the part in scope here.
`initialize` and `--probe` pay the identical cost because module-level `use`
imports resolve before `main()` runs at all, regardless of which branch of
`main()` executes afterward.

## Root cause: `main_dispatch.spl`'s handler modules load eagerly, not lazily

`src/app/mcp/main.spl:43` imports `.main_dispatch` at module scope. That one
import is unconditional even though `dispatch_tool` (the only symbol used
from it) is called from exactly one branch of the serve loop:
`elif has_method(msg, "tools/call")` (`main.spl:371`). `initialize` and
`tools/list` — the two methods every MCP client calls first, before any
`tools/call` — never reach `dispatch_tool`.

`src/app/mcp/main_dispatch.spl:1-14` in turn imports, at ITS module scope,
every one of the per-domain tool-handler modules:

```
use .main_lazy_json
use .main_lazy_diag_tools
use .main_lazy_vcs_tools
use .main_lazy_debug_tools
use .main_lazy_dialog_tools
use .main_lazy_query_tools
use .main_lazy_play_tools
use .main_lazy_assistant
use .main_lazy_node_tools
use .main_lazy_ctx_tools
use .main_lazy_telemetry
use .main_editor_tools
use .cli_passthrough
use .main_lazy_caret_tools.{is_caret_tool, handle_caret_tool}
```

Despite the `main_lazy_*` naming (and `main.spl`'s own header comment: "The
per-tool handler modules ... are reached only through dispatch_tool, so they
are imported by main_dispatch — not duplicated here"), **none of these
imports is actually lazy**. `use .main_dispatch` at `main.spl:43` pulls the
whole set in transitively at process start, before the first byte of stdin is
even read. Fourteen handler modules (debug session/breakpoint machinery,
Playwright/SDL2 drivers, the assistant task-spawn surface, node REPL, ctx
tools, telemetry, editor tools, CLI passthrough, VCS tools, caret mail/wiki/
storage) are parsed and loaded on every server start, whether or not the
client ever issues a single `tools/call`.

## Proposed fix (not applied in this change)

Move `use .main_dispatch` out of `main.spl`'s module scope and into a
function-local import inside the `tools/call` branch of the serve loop, so
the whole handler-module graph loads only on the first actual tool
invocation — `initialize`/`tools/list` (and a client that never calls a tool
at all) would no longer pay for it.

This is safe specifically **in the interpreter**, which is what this
launcher forces (`SIMPLE_EXECUTION_MODE=interpreter`, `bin/simple_mcp_server.cmd`
comment: "Interpreter mode is also FASTER to first reply here ... Seed
defect: doc/08_tracking/bug/seed_jit_some_constructor_corrupts_value_2026-09-13.md").
It is explicitly **not** safe to rely on for the native/JIT or bootstrap
compilation paths: this repo already has one closed incident where a
function-local `use` silently became a no-op under the bootstrap parser
(`doc/08_tracking/bug/stage4_devhub_wiki_function_local_process_import_2026-08-03.md`,
"the bootstrap parser deliberately consumes a function-local `use` as a
no-op statement"), and the task brief for this investigation independently
flagged that the seed JIT currently segfaults on function-local `use`. Since
`main.spl` is also `run` directly under JIT/native modes elsewhere (not just
via this interpreter-forced launcher), the fix must not change behavior on
those paths — it needs verification against a JIT/native invocation of
`src/app/mcp/main.spl`, not just the interpreter one this launcher uses,
before landing.

## Why not applied here

This host was under heavy concurrent load from other agent sessions for the
whole investigation (see the noise caveat above); a controlled, low-noise
before/after A/B (same tree, same binary, alternating trials) was not
obtainable in this session. Per the coordinator's direction, this record
ships as a breakdown with a named, scoped fix (`main.spl:43`,
`main_dispatch.spl:1-14`) rather than an unverified perf change. Landing the
fix needs: (1) apply the function-local `use .main_dispatch` move, (2) re-run
the `--probe` A/B on a quiet host, (3) separately confirm `simple.exe run
src/app/mcp/main.spl` still works under the default (non-interpreter)
execution mode, since `main.spl` is not exclusively reached through the
interpreter-forced `.cmd` wrapper.

## Non-goals ruled out during this investigation

- `tool_table.spl` / `main_static_tools.spl` (555 lines, the `tools/list`
  cache) are genuinely needed for `initialize`+`tools/list` and were not
  investigated as removable.
- No `SIMPLE_TRACE`/module-load-timing env var exists in the seed
  (`src/compiler_rust`) to get a per-module breakdown finer than the
  black-box `--probe` measurement above; adding one was out of scope.

