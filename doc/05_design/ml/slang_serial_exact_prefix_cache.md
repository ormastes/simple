# Slang serial exact-prefix cache detail design

Date: 2026-09-08. Status: implemented S1 contract.

`slang_ggml_prefix_prepare()` returns the exact token count reusable by the
next prefill. It restores only after full token equality. One trailing token is
removed and reevaluated, ensuring current boundary logits without assuming the
sequence snapshot contains sampler/output state.

`slang_ggml_eval_prompt()` evaluates `tokens[reuse_count..]`, records prefilled
tokens, then replaces the single snapshot and its token identity. Allocation
failure leaves the previous snapshot usable; serialization failure disables
the identity rather than claiming a valid entry. Teardown releases the buffer.

The Simple backend resolves capability, preparation, and four counter symbols
once during open. `PrefixCacheStats` is observable through the engine without
changing the generation result or OpenAI response schema.

Verification uses the real llama.cpp headers/library for ABI compilation and a
deterministic fake context for behavior. The fixture proves miss, exact-prefix
hit, mismatch isolation, boundary recomputation, token accounting, and cleanup.
Live latency/RSS and output-parity evidence await an admitted production Simple
runtime and a suitably small real model; no speedup is claimed yet.
