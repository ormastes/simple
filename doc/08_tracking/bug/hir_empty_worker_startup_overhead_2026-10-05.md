# HIR worker startup exceeds available module work

Status: OPEN performance investigation; no fix or speedup verified.

The new Phase 2 producer
`3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb`
compiled and ran `test/04_smoke/windows_native_hello.spl` successfully in
`runtime/windows-restart-20261004/qualification-60cd7f-warm916-hello20`.
The compile log contains 20 distinct `[hir-shard] done shard=N/20` records.
Only shard 10 lowered one module; 19 workers lowered zero modules.
This proves the explicit HIR path was exercised, not twenty useful workers
or a throughput improvement.

The qualification reports 123.162 seconds compile wall time and 12,042,164
KiB process-tree peak RSS. Empty worker startup is a plausible contributor;
these measurements do not isolate its cost from source admission, frontend
setup, cache validation, linking, or collector overhead.

Investigate capping the number of launched HIR workers by available independent
work, while preserving configured capacity (including 20, 80 and 128), owner
receipt correctness, dependency barriers, deterministic merge and crash recovery.
Do not silently change the requested job allocation or impose a fixed worker
limit. Keep active requests and caches unchanged during diagnosis.

Required regression cases: zero modules, one module, fewer modules than the
worker budget, more modules than the budget, skewed dependency levels, cache
hits, worker crash and retry. Require identical native output, unique claims,
complete receipts, no lost work and no additional memory or logic regression.
Benchmark warm and cold elapsed time plus process-tree RSS against the same
producer/source/options baseline. These cases remain UNRUN.
