# mcpgdb Non-Functional Requirements

- Startup should not eagerly launch debugger processes before the first relevant tool call.
- Workspace initialization should isolate clangd state from debug session state.
- Backend sessions must be explicitly tear-downable and temp directories removable.
- Dangerous debugger commands must be blocked by default.
- The example should remain self-contained inside `examples/mcpgdb` and avoid introducing new non-Simple source files.
