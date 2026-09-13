# LLM Dashboard Feature Expert

Created 2026-09-06: `src/app/llm_dashboard/` had no feature entry although it is
a real TUI/GUI app with its own data, collectors, scheduler, and smoke test, and
it was one of the two lanes repaired from the `e274cd33719` clobber.

## Role

Own process knowledge for the LLM dashboard (`src/app/llm_dashboard/`):
entry points, the smoke contract, and the landmines that made it silently
unrunnable.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Requirements: [kairos_like_simple_mcp_llm_dashboard.md](../../../02_requirements/nfr/kairos_like_simple_mcp_llm_dashboard.md); plan: [agent_tasks](../../../03_plan/agent_tasks/kairos_like_simple_mcp_llm_dashboard.md), [sys_test](../../../03_plan/sys_test/kairos_like_simple_mcp_llm_dashboard.md)
- Source: `src/app/llm_dashboard/` — `main.spl`, `tui_main.spl`, `tui/`, `gui/`,
  `data/` (`types.spl`, `store.spl`, `jsonl_watcher.spl`), `collectors/`, `scheduler/`
- Unit specs: `test/01_unit/app/llm_dashboard/`; integration:
  `test/02_integration/app/llm_dashboard_log_modes_spec.spl`
- Smoke: `test/03_system/tools/llm_dashboard_tui_smoke.spl`
- Layer: [app](../../layer_expert/app/skill.md)
- Related: [mcp_lsp](../mcp_lsp/skill.md), [llm_caret_messaging](../llm_caret_messaging/skill.md)

## Landmines

- **`e274cd33719` cut `data/types.spl` from 383 lines to a 104-line stub**,
  dropping 30 still-imported exports (incl. `LLMStatus`), so the TUI could not
  start. Restored byte-identically from `e274cd33719^` in `631209209f1`; the
  TUI now renders a real 7228-byte frame. **~27 more files in this app are
  still regressed by the same merge.** Before touching any of them, diff
  against `git show e274cd33719^:<file>` and restore; do not re-implement.
- **The old smoke test was a false green**: it shelled to `bin/simple run`
  (the bootstrap seed has no `run`), discarded stderr, and took its exit status
  from `| cat`. The rewritten smoke reads the binary from `SIMPLE_BINARY`
  (default `src/compiler_rust/target/bootstrap/simple`), feeds a fixture JSONL
  dir with stdin at EOF so the app draws one frame and exits through its own
  "Dashboard closed." path, captures stderr, and reads the exit status
  directly. It was proven able to fail before being trusted.

## Verification

```bash
src/compiler_rust/target/bootstrap/simple run test/03_system/tools/llm_dashboard_tui_smoke.spl
```

## Update Rule

When research, requirements, architecture, design, tests, implementation,
verification, or release artifacts change for this feature, update this file
with the new links and current handoff notes in the same commit as the work,
per `.claude/rules/vcs.md`.
