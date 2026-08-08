# Layout Framework Guide

The framework in `src/lib/common/structural/layout/` accepts flat semantic
layout inputs plus optional retained geometry and independent oracle evidence.
It discovers formatting-context/containment islands, schedules dependency SCCs
in deterministic waves, selects dirty work, and records geometry/provenance/
dispatch receipts.

Use `layout_run_full` as the correctness baseline and
`layout_run_incremental` with retained geometry plus explicit invalidated
islands. A GPU receipt is valid only when cost policy admits the batch and
submit, synchronization, readback, and independent oracle parity all succeed.
Production runs without oracle evidence reject GPU before submission. Text
measurement uses `TextMeasurePort`; the CUDA line-break proof admits only its
bounded Latin contract and rejects unsupported shaping.

Run the focused unit and system specs named in `doc/03_plan/sys_test/layout_framework.md`. Browser wiring belongs to `web_layout_manager_plan.md`; do not import browser or renderer modules into the common framework.
