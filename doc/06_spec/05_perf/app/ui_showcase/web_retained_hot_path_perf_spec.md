# Web showcase retained hot path

Source: `test/05_perf/app/ui_showcase/web_retained_hot_path_perf_spec.spl`.

The performance contract presents 100 frames at generation 1 and another 100
frames at generation 2 using the same 8K scene. Only the first frame of each
generation may serialize, and byte-identical generation advancement must not
rewrite the document. Expected totals are two serializations and one write.

This is algorithmic operation-count evidence, not an 8K latency claim. Current
p50/p95, RSS, checksum/readback, backend, binary revision, and fallback evidence
remains unavailable as recorded by
`doc/09_report/gui_renderdoc_feature_coverage_status_2026-09-02.md`; the 8K
performance outcome remains blocked until an admitted native host can run the
canonical evidence script.
