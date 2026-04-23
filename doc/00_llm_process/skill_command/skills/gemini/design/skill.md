# design

Source: `.gemini/commands/design.toml`

Cooperative Pipeline: Step 3 — UI/UX Design Primary (Gemini strengths: visual design, prototyping)
Step 1: research (any LLM) -> Step 2: requirements (any LLM) -> Step 3: design (Gemini primary) -> Step 4: impl (any LLM)

## Description

Create architecture, UI design, system tests, and detail design. Self-sufficient — if research/requirements missing, does them first.

## Prompt

Run the design pipeline for the given feature. Self-sufficient — if prerequisites missing, create them.

Check prerequisites:
- doc/02_requirements/feature/<feature>.md (if missing, run research first)
- doc/02_requirements/nfr/<feature>.md (if missing, run research first)

Phase 1: UI Design (if applicable)
- TUI: doc/05_design/<feature>_tui.md
- GUI: doc/05_design/<feature>_gui.md

Phase 2: Architecture — doc/04_architecture/<feature>.md
- For MCP, LSP, and tool servers, include startup path, hot request path, cache or index strategy, invalidation strategy, and perf budgets

Phase 3: System Test Design
- SSpec BDD tests: doc/06_spec/app/<app_name>/feature/<feature>_spec.spl
- Matchers (built-in only): to_equal, to_be, to_be_nil, to_contain, to_start_with, to_end_with, to_be_greater_than, to_be_less_than
- Every REQ-NNN must have at least one test

Phase 4: Detail Design — doc/05_design/<feature>.md

Phase 5: Quality Check — verify SSpec quality, ask user if changes needed.

If another LLM already created artifacts, review and extend — never overwrite.
Treat full-tree scans, repeated file rereads, and per-request subprocesses as design risks unless explicitly justified.
