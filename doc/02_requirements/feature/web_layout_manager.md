# Web layout manager requirements

Status: Selected by `web_layout_manager_plan.md` and the user instruction to implement it as the framework consumer.

- REQ-WLM-001: Adapt `raw_boxes` plus aligned DOM/computed-style projections into versioned structural input, preserving an explicit structural-id to DOM-route mapping.
- REQ-WLM-002: Classify style changes as `NoChange`, `InheritedOnly`, `PaintOnly`, `CompositeOnly`, `IntrinsicMeasure`, `LayoutSelf`, `LayoutSubtree`, or `RebuildFormattingContext`.
- REQ-WLM-003: Produce a stable, deduplicated per-node dirty frontier for style, insertion, font-resource, and viewport changes.
- REQ-WLM-004: Delegate full and incremental execution to the shared layout framework with family-aware resolved text requests/results; never approximate unavailable shaping.
- REQ-WLM-005: Publish boxes, fragments, line boxes, overflow, `LayoutOf`, `HitRegionOf`, and hit regions under a checked monotonically increasing epoch tied to the DOM generation.
- REQ-WLM-006: Reject stale generations and unsupported contexts explicitly.
- REQ-WLM-007: Treat GPU policy as a candidate only; publish GPU execution only after the framework validates submission, synchronization, device readback, and CPU-oracle parity.
