# Slang pure-runner specs exceed the default timeout on the seed (Windows, perf)

Measured 2026-11-24, seed simple-release.exe, Radeon 8065S. Default per-file budget is 900 s.

- slang_pure_sampling_spec: times out at 900 s (`child-timeout budget_ms=900000`);
  PASSES in 2509 s with `SIMPLE_TIMEOUT_SECONDS=3000`.
- slang_pure_kv_cache_spec: rc=124 at 3000 s (CPU stories15M under the seed interpreter).
- slang_pure_gpu_parity_spec: rc=124 at 1800 s twice (alone on the box). Evidence file shows
  the ROCm half completed (parity rel_err < 1.3e-7, greedy ids match) but the CPU reference
  alone costs 516 s for 12 tokens (0.023 tok/s) vs ROCm 3.1 tok/s (5.96 tok/s with prefix reuse
  of 7 cached positions, 503 ms vs 1637 ms fresh).
- rocm_ops: 1541 s, dominated by the CPU matvec 32000x288 reference (51.7 s vs 3.8 ms on GPU).

Not a correctness failure; the pure CPU path is the cost. Open: speed up the CPU reference or
shrink the CPU leg of these specs without weakening assertions.
