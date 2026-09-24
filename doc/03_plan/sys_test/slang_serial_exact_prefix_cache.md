# Slang serial exact-prefix cache test plan

- REQ-001/002: mismatch clears; exact token prefix restores.
- REQ-003: a four-token cached prompt reports only three reused tokens.
- REQ-004/006: teardown succeeds after snapshot creation and resets ownership.
- REQ-005: capability mask and hit/miss/reused/prefilled counters are exact.
- REQ-007: source and architecture explicitly retain single-entry serial scope.

Executable evidence:
`test/02_integration/lib/slang_prefix_cache_shim_contract_test.shs`.
ABI evidence: `scripts/check/build-slang-ggml-shim.shs` against the installed
llama.cpp SDK. Live performance evidence is a later admitted-model gate.
