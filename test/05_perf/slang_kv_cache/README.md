# Slang KV-cache matched evidence

This harness compares the existing snapshot cache with physical paged KV using
the same executable, model, prompts, token budget, and whole-process boundary.
It runs five workloads (`cold`, `exact_repeat`, `prefix_extension`,
`alternating_prefix`, and `eviction_pressure`) as five paired samples per lane.
Every sample is a fresh process; lane order alternates inside each pair.

Run:

```bash
SLANG_KV_MODEL_PATH=/models/tiny-model/model.gguf \
SLANG_KV_MODEL_ID=tiny-model \
test/05_perf/slang_kv_cache/run_matched_evidence.shs
```

Optional inputs are `SIMPLE_BIN`, `SLANG_KV_LIB`, `SLANG_KV_TOKENS`,
`SLANG_KV_THREADS` (default 1), `SLANG_KV_N_CTX` (default 4096), and
`SLANG_KV_EVIDENCE_DIR`. The output directory retains a TSV manifest, raw GNU
`time -v`/stdout/stderr receipts, a TSV summary, and a Markdown summary.
`SLANG_KV_N_CTX` must be divisible by 64; the physical pool uses exactly
`n_ctx / 64` pages so its provider context does not silently expand beyond the
matched snapshot context.

The harness fails closed. Physical samples only pass when the runtime reports
`physical_pages`; a fallback to snapshot is not benchmark evidence. A summary
is admitted only when all 50 child processes pass (five workloads times five
pairs times two lanes) and each matched pair has identical ordered generated-
text digests. Resident-request time uses a monotonic clock and excludes model
load plus a disjoint warmup. Reports include min, median, nearest-rank p95, max,
and whole-child maximum RSS. The physical lane emits page, reference, COW,
reservation, failure, and cleanup telemetry. TTFT is explicitly unavailable;
the backend API exposes only completed generation. Do not infer a speedup from
a blocked or incomplete run.
