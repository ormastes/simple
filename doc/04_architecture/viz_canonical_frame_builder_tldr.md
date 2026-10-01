# Viz canonical frame builder — TLDR

The frame builder no longer owns a parallel wire format. It emits canonical Viz
entities, so built frames can flow directly through the aggregator and display
compositor. Typed surface references become recursively imported render-pass
DAGs; the embedding quad retains placement, clip, opacity, and blend state.
Malformed/missing/cyclic dependencies fail closed. Raw legacy surface IDs are
not accepted. Each aggregate has deterministic depth/surface/pass/quad/SQS
bounds and memoizes repeated child imports, rejecting the whole frame on a
quota breach. See `viz_canonical_frame_builder.md`.
