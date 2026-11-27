# Caret Workbench UI Requirements — TLDR

Stable IDs for the Caret workbench UI program, derived from plan §13 and §11.

- Families: `REQ-CARET-UI-001..009`, `EXT-001..004`, `OBS-001..003`, `TRC-001..007`, `NFR-001..002`.
- Each row: statement, plan section, CU-001..CU-020 acceptance row, phase P0-P8.
- All proposed; none release-qualified.

```text
 UI (binding, keys, cells) --+
 EXT (manifest v2, profile) -+--> CU-001..CU-020 --> SSPEC --> CI
 OBS (axes, stall, inbox) ---+
 TRC (badges, parity, gates)-+
```

Full doc: [caret_workbench_ui.md](caret_workbench_ui.md)
Design: [../../../05_design/app/llm_caret/caret_workbench_ui.md](../../../05_design/app/llm_caret/caret_workbench_ui.md)
Plan: [../../../03_plan/app/llm_caret/caret_workbench_ui_plan.md](../../../03_plan/app/llm_caret/caret_workbench_ui_plan.md)
Research: [../../../01_research/app/llm_caret/caret_workbench_ui_research_2026-11-14.md](../../../01_research/app/llm_caret/caret_workbench_ui_research_2026-11-14.md)
