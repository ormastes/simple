# Slang exact-prefix cache shim contract

The executable C fixture creates a deterministic backend context, prefills one
prompt, extends it, and verifies that only the exact prefix is restored. It then
submits a mismatching prompt and verifies isolation through miss and token-count
evidence. The test also checks the capability mask and teardown.

**Executable evidence:**
`test/02_integration/lib/slang_prefix_cache_shim_contract_test.shs`
