# Slang prefix-cache hit decodes different greedy bytes than a full prefill

Date: 2026-11-14. Status: fixed 2026-11-15.
Tracked by: `test/03_system/lib/slang/feature/slang_kv_cache_live_exact_output_spec.spl` (now untagged and passing).

## Resolution (2026-11-15)

Root cause: batch shape of the LAST prompt token. A cold prefill decoded all
988 tokens as one batch, so the final token's hidden state (and the logits for
the first generated token) came from the large-batch kernel path; a hit
restored 987 positions and decoded the final token(s) as a batch of 1..7
(`src/runtime/slang_ggml_shim.c`, `slang_ggml_request_eval_prompt`). ggml CPU
kernels are not bit-identical across those shapes and greedy decoding flipped
on near-ties. Ruled out: sampler state (a fresh context and greedy sampler per
request, `slang_request_create_locked`), stale KV past the kept prefix (the
snapshot holds only prompt positions and `llama_memory_seq_rm` trims to
`reuse`), token mismatch (`memcmp` of token ids before restore).

Fix: `slang_ggml_request_eval_prompt` decodes `[eval_start, tok_len-1)` as one
batch and the last token alone, on both paths, so the logits always come from a
batch of 1 over the same KV. Cost: one extra single-token decode on a cold
prompt. Measured (Qwen2.5-1.5B Q4_K_M, CPU): exact_repeat 38.86x, prefix_extension
29.76x, byte-identical output in all four live workloads
(`build/probe/split_live.log`, `build/probe/split_exact.log`). The first-micro-batch
CUDA workaround keeps the single full batch.

(Original report follows.)

## Symptom

Qwen2.5-1.5B-Instruct Q4_K_M, n_ctx 2048, 12 greedy tokens, Windows mingw CPU.
With the snapshot cache on, a hit's output differs from the cache-off output
of the same prompt:

- exact_repeat (reuse 987 of 988): cache off emits
  `? Answer: request charlie owns page seven.` (42 bytes) and stops at
  end-of-generation; cache on emits the same 42 bytes and then continues with
  ` Question: ` (52 bytes).
- prefix_extension (reuse 987 of 994): differs from byte 2:
  `? Answer: Page 7 belongs to request charlie and` (on) vs
  `? Page 7 belongs to request charlie and Page` (off).

Reproduced in five of five runs. Both continuations are coherent and give the
right answer (page 7 -> charlie). Cold and disjoint prompts, where both lanes
prefill the whole prompt, are byte-identical, and cache-off is deterministic
across a repeat.

## Why it is drift, not KV corruption

- The restored KV is the byte copy `llama_state_seq_get_data` produced; the
  only difference between the lanes is how many trailing tokens are
  recomputed, and in which batch size.
- With the pre-fix shim (`slang_prefix_cache_cpu_offload_misdetect_2026-11-14.md`)
  the hit recomputed a 512-token suffix and the output was byte-identical in
  all four workloads. With a 1- or 7-token suffix it drifts. Only the batch
  shape changed.
- llama.cpp documents it: `tools/server/README.md` (`cache_prompt`), "the
  logits are **not** guaranteed to be bit-for-bit identical for different
  batch sizes (prompt processing vs. token generation)".
- A 15M-parameter model (llama2c-stories15M) shows no drift on the same
  workload.

## Options (owner)

1. Accept: a hit is equivalent, not bit-identical. Close the in-development
   spec by deleting it and saying so in the cache design docs.
2. Batch-invariant recompute: recompute a fixed-size tail, for example a full
   `n_ubatch`, so the suffix uses the same kernel path as a cold prefill. This
   costs reuse; the pre-fix numbers were 1.83x instead of ~40x.
3. Batch-invariant kernels in the backend. This is out of slang's reach today.

The green spec `slang_kv_cache_live_spec.spl` asserts identity only where it
holds (cold, disjoint, cache-off repeat). It prints `first_diff_byte` for the
hit workloads.
