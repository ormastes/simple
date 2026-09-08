# Slang physical paged-KV provider conformance

This system specification runs the native provider fixture with AddressSanitizer
and UndefinedBehaviorSanitizer. It validates the ABI's bounded ownership and
transaction rules without claiming production tensor kernels, real-model
numerical parity, or measured memory savings.

## Scenario: bounded native ownership and transaction oracle

1. Allocate bounded fixed-size pages with generation-safe identities.
2. Prefill multiple pages and publish table, cursor, and logits atomically.
3. Share sealed pages and copy a partial tail without cross-request mutation.
4. Reject uncommitted page escape, gaps, stale handles, and overflow.
5. Roll back injected writes and drain transactions during cancellation.
6. Require `STATUS: PASS slang-paged-kv-provider-conformance` from the sanitized
   native gate.

Executable source:
`test/03_system/lib/slang/feature/slang_paged_kv_backend_spec.spl`.
