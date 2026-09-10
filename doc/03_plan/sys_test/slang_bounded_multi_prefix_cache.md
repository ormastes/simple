# Slang bounded serial multi-prefix cache test plan

- REQ-001/004: two entries coexist and deterministic LRU evicts one entry.
- REQ-002/005/006: a four-byte ceiling rejects a candidate and retains zero.
- REQ-003: an extension hits the longest surviving exact prefix.
- REQ-007: every hit recomputes one boundary token; evicted input cold-starts.
- REQ-008: capability, cumulative counters, and resident gauges are exact.
- REQ-009: teardown resets ownership, counters, and bytes.
- REQ-010: architecture and capability naming remain explicitly serial.
- Failure controls inject snapshot serialization, restore, truncation, and
  decode errors; each must preserve isolation and publish no partial entry.

Executable evidence remains
`test/02_integration/lib/slang_prefix_cache_shim_contract_test.shs` using a
deterministic fake llama context. The production shim build against installed
llama headers is separate ABI evidence. Real model latency/RSS/output parity is
not claimed until an admitted self-hosted runtime and model are available.
