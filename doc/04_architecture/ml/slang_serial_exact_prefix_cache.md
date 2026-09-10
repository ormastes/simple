# Slang serial exact-prefix cache architecture

Date: 2026-09-08. Status: S1 implementation.

The ggml shim owns one model, one context, and one immutable snapshot of the
most recently prefetched prompt. Simple owns the reuse decision request flow;
the backend owns opaque execution bytes and exact tokenizer IDs.

After tokenization, `prefix_prepare` compares the cached IDs with the start of
the new prompt. A match restores the sequence snapshot, removes its trailing
token, and reports the reusable count. A mismatch or failed restore clears the
context. `eval_prompt` decodes from the selected boundary and captures the new
sequence snapshot before generation mutates live context.

This is intentionally serial and single-entry. It does not claim paged KV,
continuous batching, cross-model reuse, persistence, distributed transfer, or
non-prefix fusion. Those require immutable block identities and independent
request contexts. Capability bits distinguish resident weights (1), isolated
requests (2), and serial exact-prefix restore (4).
