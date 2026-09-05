# Executable Size Reduction Agent Tasks

Codex task breakdown, 2026-04-23.

1. Replace ELF runtime whole-archive linking with explicit runtime symbol roots.
2. Add unit coverage for root calculation.
3. Add a reusable size-budget script.
4. Wire release packaging to strip MCP/LSP native binaries and run the budget script.
5. Record local/domain research, requirements, architecture, and verification notes.
6. Split the runtime symbol ABI into a dedicated crate and remove the normal `simple-native-loader -> simple-runtime` edge.
7. Add a loader dependency-closure audit and trim unused `simple-loader` direct dependencies.
8. Add a per-binary native dependency audit covering CLI, bootstrap, and native-built package executables.
9. Use the audit to drive a follow-on architecture split that removes `simple-native-all -> simple-driver` and narrows broad default runtime services.
