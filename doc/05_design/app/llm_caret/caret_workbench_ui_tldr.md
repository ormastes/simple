# Caret Workbench UI Design — TLDR

Caret is a profile of Simple IDE, not a new IDE. smux is the only terminal multiplexer.

- Native CLIs run as real PTY children in smux; other panels are native Simple TUI/GUI views.
- Identity first: session, provider, pane, worktree bound by ID plus generation.
- Observation: structured events, then owner/process data, then screen cells, with confidence; no auto-kill.
- Traceability reuses `simple trace` and Slop; structural-only is never shown as verified.
- Extensions: additive manifest v2; keys use a `Ctrl+G` leader, `Ctrl+B` stays smux.

```text
 IDE shell -> extension host -> native views --+
                             -> smux terminals -+-> Caret service -> SOSIX/trace
```

Full doc: [caret_workbench_ui.md](caret_workbench_ui.md)
Requirements: [../../../02_requirements/app/llm_caret/caret_workbench_ui.md](../../../02_requirements/app/llm_caret/caret_workbench_ui.md)
Plan: [../../../03_plan/app/llm_caret/caret_workbench_ui_plan.md](../../../03_plan/app/llm_caret/caret_workbench_ui_plan.md)
Research: [../../../01_research/app/llm_caret/caret_workbench_ui_research_2026-11-14.md](../../../01_research/app/llm_caret/caret_workbench_ui_research_2026-11-14.md)
