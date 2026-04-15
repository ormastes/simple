# mcpgdb System Test Plan

- Verify `tools/list` contains both debugger and clangd tool families.
- Verify raw command policy blocks shell escapes and ungated mutations.
- Verify session registry supports create, select, list, and close flows.
- Verify workspace open/status flows return expected root and compile command state.
- On machines with debugger binaries available, smoke-test `debug_session_create` and one no-target read-only command.
