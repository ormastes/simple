# Widget Draw IR text coverage and memory — 2026-08-26

The focused glyph-run suite passes 4/4. Direct coverage is 42% lines (103/240)
and 15% branches (8/51) for `src/lib/common/ui/widget_draw_ir.spl`. It proves a
positive Latin glyph payload reaches v3 Draw IR and rasterization, plus the
zero-glyph anti-vacuity case.

The complementary widget suite passes 10/10. A final three-suite union emitted
`build/coverage/widget_draw_ir_union_cycle3.sdn`, but the artifact records only
parent runner coverage (408/408 lines, 12/63 decisions). Child owner counters
were not merged, so those numbers are non-admissible for this owner. The direct
42%/15% result remains authoritative and the owner remains open after the
three-cycle cap.

No widget memory-performance claim is available. Required future native
receipts are p50/p95 latency, throughput, allocation count and bytes, peak and
steady RSS delta, font/glyph cache retained bytes, copied glyph bytes, atlas
bytes (if downstream work is included), and post-cleanup retention. Parent
runner RSS and interpreter suite duration must not be substituted for these
owner-attributed counters.
