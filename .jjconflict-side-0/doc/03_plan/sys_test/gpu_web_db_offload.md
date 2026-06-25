<!-- codex-design -->
# GPU Web and DB Offload System Test Plan

Status: recovered design draft.

## Planned Specs

- `test/03_system/app/http_server/feature/gpu_web_db_offload_spec.spl`
- `test/03_system/lib/database/feature/gpu_web_db_offload_spec.spl`
- `test/05_perf/web_db/gpu_web_db_offload_perf_spec.spl`

## Required Cases

- proxy route uses upstream config and bypasses buffered content handler;
- upstream timeout/error paths produce explicit proxy errors;
- hop-by-hop headers are stripped or rewritten;
- upstream pooling avoids per-request connect under reuse conditions;
- no-GPU host reports CPU fallback for web and DB workloads;
- GPU evidence backend reports hit only when enabled;
- queue-full and stale-generation paths fall back or error by policy;
- RAM mode rejects over-budget GPU batches without data loss;
- SSD mode preserves WAL/reopen behavior and rejects stale accelerated reads;
- NoSQL/vector mode returns the same logical results for CPU and GPU-hit paths;
- tiny batches are rejected for GPU performance claims.

## Pass/Fail

No placeholder passes. No `expect(true).to_equal(true)`. GPU specs must assert
both CPU fallback and GPU-hit states.
