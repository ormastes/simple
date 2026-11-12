# slang: CUDA illegal memory access on a fresh context's short first micro-batch

- Date: 2026-11-12
- Severity: P1 (aborts the whole slang server process)
- Status: worked around in `src/runtime/slang_ggml_shim.c` (`slang_request_warm`); root cause is upstream
- Host: DGX Spark GB10, aarch64, CUDA 13; llama.cpp b10794; Qwen3-Coder-30B-A3B Q4_K_M; n_ubatch 512

## Symptom
After hours of serving two caret agents, the server aborted (rc=134):
`state_read_meta: cell_count = 15809` followed by
`CUDA error: an illegal memory access ... ggml_cuda_kernel_launch` (Xid 31, FAULT_PDE VIRT_READ).

## Cause
This is not the prefix restore. A freshly created context aborts inside `llama_decode` when its
first micro-batch has certain sizes below `n_ubatch`. A sweep of 206 cold sizes crashed at 2
of them, with no restore involved. The same sizes are harmless once the context has run one full
micro-batch. A prefix restore is what leaves a short suffix as a context's first decode.
The fault is probably the upstream CUDA MMQ MoE buffer-padding fault fixed in a later llama.cpp
release. This has not been verified against the local checkout.

## Workaround
A context that has never decoded a full micro-batch first runs a throwaway full micro-batch, and a
restore gives reuse back until its suffix is one full micro-batch. The rule applies only to
GPU-offloaded models with `n_ubatch < n_ctx`.
Cost: up to 512 extra prefill tokens on short or restored requests (about 0.9–1.4 s instead of 0.7–0.95 s).
Result: 0 crashes in 410 requests, against a 2-in-206 crash rate before the fix.

## Remove when
llama.cpp is upgraded past the MoE MMQ padding fix, and a cold-prompt size sweep
(prompts of 1..600 filler words against a real CUDA server) passes with `slang_request_warm`
disabled. The mock-backed rules are pinned by
`test/02_integration/lib/slang_prefix_cache_shim_contract_test.shs`.
