# Layout Framework Detail Design — TLDR

- Flat ordered node snapshot; oracle geometry stays authoritative.
- Boundary nodes form islands; work is summed per island.
- SCCs become deterministic topological waves.
- Incremental runs name every visited island.
- GPU choice includes transfers and synchronization; inline stays CPU.

<!-- sdn-diagram:id=layout-framework-design-tldr -->
```sdn
run: {discover: islands, schedule: scc_waves, execute: cost_policy, verify: geometry_and_receipts}
```

