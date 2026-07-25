# LLM Caret Claude CLI Harden - Architecture

Date: 2026-07-05

## Decision

Treat `src/app/llm_caret` as one MDSOC+ app-layer provider caret. Claude CLI
feature migration lands through explicit provider modules and trace tables,
not by importing the full Claude CLI UI, remote bridge, or OAuth subsystem.

## Boundaries

- App provider caret: `src/app/llm_caret`.
- External comparison source: `tmp/claude/claude-code-main/src`.
- Verification: shell checker plus SSpec system gate.

## Invariants

- Provider source files must stay mapped to Claude source evidence or an
  explicit Simple-only extension role.
- File and LOC mapping coverage must remain at least 80%.
- Function, struct, and extern symbol trace coverage must remain complete.
- The default gate must be offline and deterministic.

## TUI Runtime Boundary (2026-07-24)

The shipped interactive loop is split across two app-layer capsules:

- `tui_io.spl` owns the `CaretIo` capability bundle and its production
  adapters to the canonical terminal and stdin owners.
- `chat_tui.spl` owns rendering, input reduction, session transitions, and
  lifecycle ordering. Tests inject a `CaretIo`; they do not copy this logic or
  declare private runtime externs.

Raw mode is acquired before alternate-screen or cursor mutation. Every modeled
exit restores cursor visibility, alternate-screen state, and raw mode in that
order. A raw-entry failure is returned as a typed loop result and becomes a
nonzero CLI exit. Frame rendering takes one terminal-size snapshot so a resize
cannot mix dimensions from two queries.

Hard panics and asynchronous signals remain below the app-layer capability
boundary: full restoration for those paths requires a runtime-owned
atexit/signal guard and must not be claimed from component tests.
