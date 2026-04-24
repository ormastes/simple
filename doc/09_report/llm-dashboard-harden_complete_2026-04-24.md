# llm-dashboard-harden -- Completion Report

**Date:** 2026-04-24
**Pipeline:** SStack 8-phase

## Summary

Hardened the LLM dashboard so it works robustly on CLI, GUI, and SimpleOS surfaces. Integrated task_daemon pipeline events into the dashboard view. Homogenized generator tool schemas across MCP tool_table and cli_passthrough.

## Architecture

Key decisions:

- **D-1:** run_serve/run_gui/run_agents stubs in dashboard/main.spl delegate to run_llm_dashboard() — reuses existing arg parsing, avoids duplicating server logic
- **D-2:** has_tauri_shell() defined in src/app/ui/detect.spl — consistent with existing platform probes; returns false on SimpleOS
- **D-3:** --browser guard: only invoke shell_open if platform != "simpleos"; otherwise print URL
- **D-4:** New TaskKind.Job variant for task_daemon entries (one-shot jobs, not Daemon/Loop)
- **D-5:** task_daemon_collector is a separate file from schedule_collector (different store format)
- **D-6/D-7:** Generator descriptions follow "[cli] Regenerate <outputs> from <source-db>" template; vestigial name param removed from feature_gen/task_gen; required_json added to path-taking tools; todo_gen gets read_only=true

## Files

- **Specs:**
  - `test/unit/app/dashboard/dashboard_serve_spec.spl`
  - `test/unit/app/ui/detect_spec.spl`
  - `test/unit/app/llm_dashboard/collectors/task_daemon_collector_spec.spl`
  - `test/unit/app/llm_dashboard/data/types_taskkind_spec.spl`
  - `test/unit/app/mcp/tool_table_generators_spec.spl`
  - `test/unit/app/mcp/cli_passthrough_spec.spl`

- **Implementation (new):**
  - `src/app/llm_dashboard/collectors/task_daemon_collector.spl`
  - `src/app/llm_dashboard/tui/tasks_panel.spl`

- **Modified:**
  - `src/app/dashboard/main.spl` — replaced run_serve/run_gui/run_agents stubs; fixed double-port bug
  - `src/app/llm_dashboard/data/types.spl` — TaskKind.Job variant + task_kind_name arm
  - `src/app/llm_dashboard/collectors/__init__.spl` — re-export collect_task_daemon_tasks
  - `src/app/llm_dashboard/gui/tasks_panel_html.spl` — wire in task_daemon collector
  - `src/app/mcp/tool_table.spl` — fix feature_gen/task_gen entries; add required_json to path tools; add todo_gen read_only
  - `src/app/mcp/cli_passthrough.spl` — remove vestigial name passthrough for feature_gen/task_gen

## Verification

- Tests: 39/39
- Failures: 0
- Lint: clean (bin/simple build lint — only pre-existing Rust clippy warnings)
- Build: PASS (bin/simple build check exits 0)

## AC Coverage

| AC | Status |
|----|--------|
| AC-1: gui no "temporarily unavailable" | PASS |
| AC-2: serve exposes web view | PASS |
| AC-3: TUI on SimpleOS QEMU, no Tauri dep | PASS |
| AC-4: task pipeline visible in dashboard | PASS |
| AC-5: generators homogenized | PASS |
| AC-6: build passes | PASS |
| AC-7: surface_alignment counts unchanged (CLI=70, MCP=99) | PASS |

## Timeline

| Phase | Status | Date |
|-------|--------|------|
| 1. Intake | done | 2026-04-24 |
| 2. Research | done | 2026-04-24 |
| 3. Architecture | done | 2026-04-24 |
| 4. Spec | done | 2026-04-24 |
| 5. Implement | done | 2026-04-24 |
| 6. Refactor | done | 2026-04-24 |
| 7. Verify | done | 2026-04-24 |
| 8. Ship | done | 2026-04-24 |
