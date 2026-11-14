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

## Live snapshot-cache evidence, Windows mingw CPU, 2026-11-14

Lane: snapshot / exact-prefix cache (S1-S3). The physical-pages lane was not
run: the local llama.cpp (`/c/dev/tools/llama.cpp`, `99b9548`) has no
`include/llama-slang-paged.h`, so the shim compiles with
`SLANG_HAS_EXTERNAL_PAGED_PROVIDER 0` and does not advertise capability bit 5
(physical paged KV).

- Spec: `test/03_system/lib/slang/feature/slang_kv_cache_live_spec.spl`. One
  process, the model loaded once, the same request sequence (cold A,
  exact_repeat A, prefix_extension A+ext, disjoint D) with
  `engine_set_prefix_cache_limits(0, 0)` and then `(4, 2147483648)`.
- Runner: Rust seed `/c/dev/simple/bin/simple.exe`, 37622272 bytes, Nov 12
  21:49, sha256 `e1128889cc709e5e9b3204bb4fae23831a93515370c89bab6e065fb2216f58c5`.
- Shim: `src/runtime/slang_ggml_shim.c` built with llvm-mingw clang against
  `build-mingw` llama.cpp (CPU only).
- Model: `Qwen2.5-1.5B-Instruct-Q4_K_M` (986048768 bytes), n_ctx 2048,
  max_tokens 12, greedy.
- `*_ms` is resident request wall time from a monotonic clock: prefill plus the
  same 12-token decode budget. `prompt_tokens_*` and `hits` are deltas of the
  shim's own `slang_ggml_prefix_tokens_prefilled` / `_hits` counters.
- Command: `PATH="$PWD/build/sffi:$PATH" SLANG_MODEL_ROOT=C:/dev/model
  SLANG_LIVE=1 SLANG_KV_MODEL_ID=Qwen2.5-1.5B-Instruct-Q4_K_M
  /c/dev/simple/bin/simple.exe test <spec>`. On Windows the `PATH` entry lets
  `slang_ggml.dll` find `libllama.dll`/`ggml*.dll` and the llvm-mingw runtime
  DLLs copied next to it.

Run 1 (spec PASS):

| workload | off_ms | on_ms | speedup | prompt_tokens_off | prompt_tokens_on | hits |
|---|---|---|---|---|---|---|
| cold | 56244 | 54783 | 1.02x | 988 | 988 | 0 |
| exact_repeat | 53540 | 1344 | 39.83x | 988 | 1 | 1 |
| prefix_extension | 51792 | 1769 | 29.27x | 994 | 7 | 1 |
| disjoint | 13421 | 14493 | 0.92x | 259 | 259 | 0 |

Run 2 (spec PASS):

| workload | off_ms | on_ms | speedup | prompt_tokens_off | prompt_tokens_on | hits |
|---|---|---|---|---|---|---|
| cold | 53034 | 50856 | 1.04x | 988 | 988 | 0 |
| exact_repeat | 53138 | 1193 | 44.54x | 988 | 1 | 1 |
| prefix_extension | 53285 | 1532 | 34.78x | 994 | 7 | 1 |
| disjoint | 14109 | 13360 | 1.05x | 259 | 259 | 0 |

Same model and spec with the shim as it was before this change (CPU offload
misdetect, `doc/08_tracking/bug/slang_prefix_cache_cpu_offload_misdetect_2026-11-14.md`):
exact_repeat 988 -> 512 prompt tokens, 51170 -> 27942 ms (1.83x);
prefix_extension 994 -> 512, 1.85x. That run's output was byte-identical in
all four workloads (one run). On this host the trade is about 40x with drift
on hits versus 1.8x without it; the owner decides.

Output: cold and disjoint are byte-identical across lanes. The hit workloads
drift (first differing byte 42 for exact_repeat, 2 for prefix_extension) once
the recomputed suffix is 1-7 tokens. That is ggml batch-shape
non-invariance, not KV corruption; see
`doc/08_tracking/bug/slang_prefix_cache_hit_output_drift_2026-11-14.md` and the
in-development `slang_kv_cache_live_exact_output_spec.spl`.
