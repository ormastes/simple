# Slang physical paged-KV provider conformance

This system specification runs the native provider fixture with AddressSanitizer
and UndefinedBehaviorSanitizer. It validates the ABI's bounded ownership and
transaction rules without claiming production tensor kernels, real-model
numerical parity, or measured memory savings.

The separate production qualification gate
`scripts/check/check-slang-ggml-real-paged-provider.shs` binds the same ABI to a
compatible llama.cpp checkout and a real GGUF model. The Simple-owner smoke then
proves four-token cold and exact-repeat generation, equal output, observed cache
hit/miss telemetry, repeated COW decode, and zero retained owner state after
shutdown. These environment-bound checks supplement this portable sanitized
scenario; they are not synthesized by it.

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

Exercised clauses: the portable conformance oracle checks bounded page identity,
namespace isolation, transactional publication/rollback, COW isolation, stale
handle rejection, and cancellation cleanup from
REQ-002/003/004/007/009/011/012/014. The real-provider and Simple-owner smoke
checks explicit opt-in activation, cold generation, an exact-prefix repeat,
observed hit/miss telemetry, repeated COW decode, and shutdown cleanup from
REQ-001/004/005/009/010/011/012/013/014/015.

These checks do not yet constitute exhaustive coverage of every activation
fallback branch or every incompatible-configuration rejection. Equal generated
tokens in the deterministic smoke are a repeatability check, not full
logit-level or numerical-parity proof. Those broader qualification clauses and
comparative performance acceptance remain open until dedicated evidence exists.
