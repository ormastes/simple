# slang pure GPU forward: per-token latency far below GPU capability (2026-11-23)

Measured with the pinned seed (sha a2e9dd36) on the Radeon 8065S, stories15M F32,
spec `slang_pure_gpu_parity_spec.spl` (log: C:/dev/slang-logs/gpuall-h2/run3.log).

| run | tokens/s |
|---|---|
| CPU pure forward (seed interpreter) | 0.021 (12 tokens, 573 s) |
| GPU first run (incl. kernel compile) | 2.5 (18 tokens, 7.1 s) |
| GPU, prefix-reuse request | 5.5 (3 tokens, 0.54 s) |

A 15M model on a GPU should exceed hundreds of tokens/s. About 20 kernel launches
per layer per token, each followed by host round trips and per-op alloc/free in
`llama_step_gpu`, plus a single-block argmax/matvec design, bound the rate.
Not fixed here (parity lane); candidates: fuse ops, reuse step buffers, batch
prompt positions.
