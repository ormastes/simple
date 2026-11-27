# Seed JIT: large compile-time-constant [0u8; N] blows up (2026-11-27)

Status: open, P3. Seed: /home/yoon/.cache/cargo-target-wr-seed1126b/release/simple, SIMPLE_EXECUTION_MODE=jit.

## Repro
`var out: [u8] = [0u8; 16777216]` (literal constant size) in `main`: no result after 600 s, 16 GB RSS.
`val n = 16777216` taken from runtime input, or `n` of 1M/4M computed at runtime: 0.02 s, about 50-80 MB.
The constant is probably expanded element by element at compile time.

## Impact
No library code is affected; library buffers are sized at runtime. Perf drivers avoid constant sizes.
