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
