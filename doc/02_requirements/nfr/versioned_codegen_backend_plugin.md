# Versioned codegen backend plugin NFRs

<!-- codex-design -->

- NFR-001: Built-in provider selection adds at most 2 ms warm startup latency.
- NFR-002: Dynamic admission adds at most 20 ms warm startup latency, excluding
  operating-system cold page faults.
- NFR-003: Selection performs no recursive source scan or subprocess launch.
- NFR-004: A provider is opened once per compilation/execution session; hot MIR
  operations use the retained function table and opaque handle.
- NFR-005: ABI mismatch, missing symbol, unsupported role/target, and digest
  mismatch produce stable diagnostics without leaks or partial artifacts.
- NFR-006: Provider teardown is idempotent and releases every provider-owned
  session/module allocation.
- NFR-007: Equivalent explicit configuration produces byte-stable admission
  receipts and stable backend choice.

