# LLM Caret Claude CLI Full Parity - System Test Plan

Date: 2026-07-05

## Required System Specs

- `test/03_system/tools/llm/claude_full/full_parity_inventory_spec.spl`
  proves matrices still cover the current Claude source tree.
- `test/03_system/tools/llm/claude_full/core_cli_runtime_spec.spl`
  covers P1 entry, query, tools, state, schemas, CLI IO, and cost/token behavior.
- `test/03_system/tools/llm/claude_full/commands_tools_spec.spl`
  covers every command/tool row.
- `test/03_system/tools/llm/claude_full/terminal_ui_spec.spl`
  captures TUI-visible parity for components, screens, hooks, keybindings, vim,
  buddy, voice, and status surfaces.
- `test/03_system/tools/llm/claude_full/remote_bridge_spec.spl`
  covers bridge, remote, server, trusted-device, session-runner, and transports
  with fake transports plus opt-in live gates.
- `test/03_system/tools/llm/claude_full/services_plugins_skills_spec.spl`
  covers services, plugins, skills, memory, output styles, telemetry, and
  migrations.
- `test/03_system/tools/llm/claude_full/support_utilities_spec.spl`
  covers support utility rows and platform behavior.

## Inventory Spec Assertions

- source file count equals file matrix rows;
- extracted symbol count equals symbol matrix rows;
- feature matrix has no empty target capsule or done gate;
- no matrix row contains skip/defer markers;
- every file row target minimum LOC is at least source LOC;
- every file row has a primary test path;
- every symbol row has a target Simple symbol and test gate.
