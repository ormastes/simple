# Slang physical paged-KV system test plan

Date: 2026-09-08.

Trace every REQ-NNN through a native provider fixture and, when available, a real
small-model numerical run. Required scenarios: cold request; aligned shared fork;
partial-tail COW; interleaved request parity; exact-token hash collision; every
execution-namespace mismatch; pinned eviction and shrink; stale page/pool/request
handles; cancellation; unload; allocation/copy/decode failure rollback; partial
ABI fallback; and physical-memory comparison against S3.

The executable conformance spec lives at
`test/03_system/lib/slang/feature/slang_paged_kv_backend_spec.spl`, with the
mirrored manual at
`doc/06_spec/03_system/lib/slang/feature/slang_paged_kv_backend_spec.md`. Its
sanitized native fixture covers ownership and failure semantics. Real-model
numerical parity and physical-memory comparison remain promotion gates.

Promotion requires native fixture PASS, sanitizer PASS, numerical parity,
observable boundedness, real physical-memory savings, and explicit confirmation
that telemetry says `physical_pages` rather than `shared_sequence` or `snapshot`.
