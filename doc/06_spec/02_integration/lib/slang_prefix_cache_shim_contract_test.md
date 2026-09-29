# Slang exact-prefix cache shim contract

The executable C fixture creates a deterministic backend context, configures a
two-entry byte-bounded cache, alternates prompts, and verifies longest exact
prefix selection and deterministic LRU eviction. It checks boundary-token
recomputation, counters, resident gauges, oversized rejection, and teardown.
Injected serialization, restore, truncation, and decode failures prove that a
partial snapshot is never published and the next cold request is isolated.

**Executable evidence:**
`test/02_integration/lib/slang_prefix_cache_shim_contract_test.shs`
