# Layout Framework Detail Design — TLDR

- Flat ordered semantic snapshot; oracle geometry is a separate verification channel.
- Boundary nodes form islands; CPU/GPU costs are recorded per island.
- SCCs become deterministic waves whose executed geometry hashes prove convergence.
- Incremental runs name every visited island.
- GPU choice includes transfer/sync and becomes execution only after device readback parity.
- Initial device packing is limited to fixed childless block/flex/grid roots.

<!-- sdn-diagram:id=layout-framework-design-tldr -->
```sdn
run: {discover: islands, schedule: scc_waves, execute: consumer_ports, verify: oracle_and_receipts}
```
