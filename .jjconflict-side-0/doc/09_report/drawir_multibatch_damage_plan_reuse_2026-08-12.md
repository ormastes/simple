# DrawIR Multi-Batch Damage Plan Reuse — 2026-08-12

Status: **CORRECTNESS PASS / STRUCTURAL ALLOCATION REDUCTION / TIMING UNPROVEN**

The retained composition executor previously called plain-fill coalescing for
every intersecting `(damage rectangle, batch)` pair. Coalescing depends only on
the immutable batch command list, so a frame with `D` damage rectangles and `B`
batches rebuilt up to `D * B` plans.

The executor now builds at most one immutable command plan per batch, lazily on
that batch's first damage intersection, then indexes those plans while
preserving the original damage-major and batch-major paint order. Untouched
batches retain the old zero-planning behavior. Clip installation, CSS pixel-work
budget consumption, unsupported-kind receipts, and conservative rejection of
translucent or parent-sampling embeddings are unchanged. Damage validation
continues to reject overlapping rectangles.

A focused disjoint-damage, two-batch scenario compares the complete retained
framebuffer with an uncropped full redraw and pins three rendered logical
operations with zero skipped operations. The full DrawIR advanced spec exited
successfully with the change.

The available executable is a Rust bootstrap seed and did not produce a usable
timing receipt for the existing 8K benchmark. This report therefore claims only
the source-level bound of at most one coalescer invocation per touched batch and
its pixel/receipt parity. It does not claim reduced container-copy cost, an 8K
latency improvement, or an end-to-end 80 fps result.
