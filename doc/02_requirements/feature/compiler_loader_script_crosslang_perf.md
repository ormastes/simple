# Compiler, loader, script, and cross-language performance requirements

Selection: retained feature contract (bounded Build9 tranche).

- REQ-001: Every retained row preserves equivalent input semantics and a checked output checksum; failed or fallback execution is rejected or explicitly unavailable.
- REQ-002: Available C, Rust, Go, Python, and Bun producers are represented in the retained comparison; missing toolchains remain visible as unavailable.
- REQ-003: Simple evidence requires canonical self-hosted executable identity, admitted Stage 3/4 provenance, and stub fallback disabled.
- REQ-004: The interpreter resolver caches successful and unsuccessful results until its explicit reset boundary.
- REQ-005: Caller-sensitive relative misses remain distinct; only eligible module families use the module-only fast cache.
- REQ-006: Repeated miss, adjacent caller miss-to-hit, and reset-generation behavior have executable regression coverage.
- REQ-007: Existing resolver search order, public APIs, errors, and outputs remain unchanged.
- REQ-008: Native packed-byte rows prove exact 1, 4, and 32 MiB lengths, zero-fill boundaries, and checksum; the native execution mode is explicit.
- REQ-009: The native byte fixture reports comparable fixture wall time and enforces the existing `<1 s` 1 MiB and `<30 s` 32 MiB targets; the retained report separately records process wall samples.
