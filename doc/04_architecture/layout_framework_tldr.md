# Layout Framework Architecture — TLDR

- Pure-Simple `common.structural` capsule; browser layout remains the oracle consumer.
- Typed node semantics cross one `LayoutExecutionPort`; oracle boxes stay host-side verification evidence.
- SCC-condensed waves execute until geometry stabilizes or the positive cap faults.
- GPU candidacy uses summed per-island cost; GPU receipt requires submit/sync/readback/oracle proof.
- CUDA currently admits exact fixed-leaf block/flex/grid islands and pre-rejects wider shapes.
- Inline sends a family-aware request through `TextMeasurePort`; no shaping approximation.

<!-- sdn-diagram:id=layout-framework-architecture-tldr -->
```sdn
flow: [contracts, islands, scc_waves, execution_port, oracle_verify, snapshot_receipt]
```
