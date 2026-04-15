# SStack State: gdb-cli-interface

## User Request
> gdb like cli interface support impl specially output text format.

## Task Type
feature

## Refined Goal
> Add a GDB-like interactive CLI debug command (`bin/simple debug`) that provides a `(sdb) ` prompt with GDB-compatible commands (break, run, next, step, print, bt, info, etc.) and human-readable text output formatting. The CLI wraps the existing mcpgdb/debug infrastructure — no new debug engine needed, just a user-facing text interface layer.

## Acceptance Criteria
- [ ] AC-1: `bin/simple debug <program>` launches interactive debug session with `(sdb) ` prompt
- [ ] AC-2: Core GDB commands work: `break`/`b`, `run`/`r`, `continue`/`c`, `next`/`n`, `step`/`s`, `finish`, `quit`/`q`
- [ ] AC-3: Inspection commands work: `print`/`p`, `backtrace`/`bt`, `info locals`, `info breakpoints`, `info threads`, `frame`/`f`, `list`/`l`
- [ ] AC-4: Output is human-readable GDB-style text (not JSON), e.g. breakpoint hits show `Breakpoint 1, main() at file.spl:42`, stack traces show `#0 func_name (args) at file:line`
- [ ] AC-5: Command registered in `src/app/cli/dispatch/table.spl` as `"debug"` entry
- [ ] AC-6: Help command (`help`, `help break`, etc.) prints GDB-style usage

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Key Files
- **Template:** `src/app/repl/main.spl` (REPL loop pattern)
- **Backend:** `src/app/mcpgdb/debug_backend_common.spl` (prompt/output handling)
- **GDB MI parser:** `src/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser.spl`
- **CLI dispatch:** `src/app/cli/dispatch/table.spl`
- **New app:** `src/app/cli_debug/main.spl` (to create)

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-04-11
- [x] 2-research (Analyst) — 2026-04-11 (inline — research from prior exploration)
- [x] 3-arch (Architect) — 2026-04-11 (inline — REPL + mcpgdb backend pattern)
- [ ] 4-spec (QA Lead)
- [x] 5-implement (Engineer) — 2026-04-11
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Refined goal:** GDB-like interactive CLI (`bin/simple debug`) with human-readable text output formatting, wrapping existing mcpgdb debug infrastructure.

**Key decisions:**
- Prompt: `(sdb) ` (Simple Debugger, avoids conflict with actual gdb)
- Reuse existing REPL pattern from `src/app/repl/main.spl`
- Dispatch GDB commands → mcpgdb session management / debug library calls
- Output formatting module: convert structured debug data → GDB-style text
- Register as `debug` command in CLI dispatch table

**Scope:** Text interface layer only — no changes to debug engine, DAP, or mcpgdb.

### 2-research
Research done via Explore agent — found:
- No existing debug CLI command in dispatch table
- mcpgdb backend at `src/app/mcpgdb/debug_backend_common.spl` provides session management + command execution
- GDB MI parser exists at `src/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser.spl`
- REPL template at `src/app/repl/main.spl` — input/eval loop pattern
- Output from `run_session_command()` returns JSON `{"status":"ok","output":"<gdb text>"}`

### 3-arch
Architecture: 3-file app structure
- `src/app/cli_debug/main.spl` — REPL loop, CLI arg parsing, banner
- `src/app/cli_debug/commands.spl` — command dispatch (GDB aliases → backend calls)
- `src/app/cli_debug/format.spl` — human-readable output formatting (ANSI colors, GDB-style text)
- Wraps mcpgdb backend — creates gdb session, sends commands via `run_session_command()`
- Unknown commands passed through to backend directly

### 4-spec
<pending>

### 5-implement
Files created:
- `src/app/cli_debug/main.spl` — REPL with `(sdb) ` prompt, CLI arg parsing
- `src/app/cli_debug/commands.spl` — 20+ GDB commands with aliases (r/c/n/s/b/p/bt/f/l/i/q)
- `src/app/cli_debug/format.spl` — ANSI-colored GDB-style output (breakpoints, frames, variables, source, help)
- `src/app/cli/dispatch/table.spl` — registered `"debug"` command entry

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
