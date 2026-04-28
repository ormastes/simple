# Executable Size Reduction - Feature Requirements

Codex final requirements, 2026-04-23.

- REQ-001: ELF native-build links must not force-load `libsimple_native_all.a` by default.
- REQ-002: ELF native-build links must retain runtime symbols required by generated object undefined references.
- REQ-003: ELF native-build links must retain known runtime lifecycle, argument, dispatch, string, and array roots that can be reached indirectly.
- REQ-004: A diagnostic environment override must preserve legacy whole-archive runtime linking.
- REQ-005: Release package native MCP and LSP binaries must be stripped.
- REQ-006: A reusable size-budget script must check CLI, MCP, LSP, generated native executable, and runtime archive artifacts.
- REQ-007: `simple-native-loader` must not have a normal dependency on `simple-runtime`; it must consume a dedicated runtime-symbol ABI crate instead.
- REQ-008: The runtime-symbol ABI crate must own `AbiVersion`, `RuntimeSymbolProvider`, `RUNTIME_SYMBOL_NAMES`, and the static symbol-registration contract used by loader static mode.
- REQ-009: A repeatable loader dependency audit command must fail if `simple-native-loader` regains `simple-runtime` on its normal dependency tree or if loader-crate direct dependencies drift from the documented allowlists.
- REQ-010: `simple-loader` direct dependencies must exclude unused hashing and serialization crates unless the loader sources reintroduce a direct need for them.
