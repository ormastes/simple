# Executable Size Reduction - Feature Requirements

Codex final requirements, 2026-04-23.

- REQ-001: ELF native-build links must not force-load `libsimple_native_all.a` by default.
- REQ-002: ELF native-build links must retain runtime symbols required by generated object undefined references.
- REQ-003: ELF native-build links must retain known runtime lifecycle, argument, dispatch, string, and array roots that can be reached indirectly.
- REQ-004: A diagnostic environment override must preserve legacy whole-archive runtime linking.
- REQ-005: Release package native MCP and LSP binaries must be stripped.
- REQ-006: A reusable size-budget script must check CLI, MCP, LSP, generated native executable, and runtime archive artifacts.
