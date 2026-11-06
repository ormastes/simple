# Bootstrap host reserve architecture

The CLI shard-memory policy owner remains `app.cli.shard_mem_clamp`. Its pure
`shard_effective_tree_budget_kb_v1` helper combines resource bounds; OS probes,
host configuration, and enforcing watchdogs retain their existing ownership.
No new module, interface or dependency is needed.

For known host free memory, the effective budget is the minimum of host free
minus reserve and each positive declared/enforced compiler cap. For unknown
host free, the existing cap-minus-reserve fallback remains. Parent reservation
and per-worker sizing continue in the existing admission layer. The refusal
message describes the revised formula without changing the refusal decision.

The fix needs no MCP/LSP startup, cache, or language-surface changes. It does not
admit a producer, publish a runtime, or replace bootstrap qualification.
