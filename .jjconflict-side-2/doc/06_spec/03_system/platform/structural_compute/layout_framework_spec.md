# Layout framework system evidence

Status: manual companion; executable source is `test/03_system/platform/structural_compute/layout_framework_spec.spl`.

The scenario proves deterministic island discovery, dependency waves, bounded convergence, exact CPU-oracle boxes, incremental island selection, `LayoutOf` mappings, receipts, GPU cost admission, rejection of incomplete device claims, and explicit CPU fallback.

Live device companion: `test/02_integration/rendering/web_layout_cuda_live_spec.spl` uploads typed fixed-leaf semantics, dispatches CUDA PTX for block/flex/grid batches, synchronizes, reads `{id,x,y,width,height}` from device memory, and requires exact oracle parity before accepting the GPU receipt.

The web layout manager scenario is the first concrete consumer and checks that browser oracle geometry survives full and incremental framework execution unchanged.

Runtime execution remains held until an eligible canonical pure-Simple CLI restores `test`; the executable specs contain real assertions and no placeholder passes.
