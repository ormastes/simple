# Layout Framework Guide

The framework in `src/lib/common/structural/layout/` accepts flat layout inputs whose geometry comes from a consumer's CPU oracle. It discovers independent formatting-context/containment islands, schedules dependency SCCs in deterministic waves, selects dirty work, and records geometry/provenance/dispatch receipts.

Use `layout_run_full` as the correctness baseline and `layout_run_incremental` only with an identical input snapshot plus explicit invalidated islands. Compare the returned boxes structurally. A GPU receipt is valid only for a homogeneous block/flex/grid batch whose total predicted latency, including transfer and synchronization, is lower than CPU. Inline/text work requires `TextMeasurePort` and remains CPU-selected.

Run the focused unit and system specs named in `doc/03_plan/sys_test/layout_framework.md`. Browser wiring belongs to `web_layout_manager_plan.md`; do not import browser or renderer modules into the common framework.

