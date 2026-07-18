# Claude Full Insights Command Spec

Mirrors `test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl`.

## Coverage

- Command metadata: `local-jsx`, `insights`, visible, interactive-only.
- Source parity floor: `insights.spl` is at least 3200 lines and reports 3200 modeled upstream lines.
- Metrics: analyzes only sessions from the last 30 days.
- Report generation: emits HTML, report path, browser-open success and fallback.
- Failure branches: no local sessions, noninteractive mode, and write failure.

## Evidence

`bin/simple test test/03_system/tools/llm/claude_full/commands/insights_command_spec.spl --mode=interpreter`

Result: 4 examples, 0 failures.
