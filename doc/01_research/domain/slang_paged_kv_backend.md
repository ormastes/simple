# Slang paged-KV backend domain research

Date: 2026-09-08. Reviewer: Astra. Inspected llama.cpp revision: `f9f09f0`.

`llama_state_seq_get_data` and `llama_state_seq_set_data` serialize or restore a
complete opaque sequence state. Byte ranges of that serialization are not KV
pages and cannot be independently attached to token positions.

Within one unified llama context, `llama_memory_seq_cp` shares actual KV cells by
sequence metadata, but the public API exposes no physical page allocator or page
table. It returns no allocation/failure status, partial copying across separate
KV streams can assert, and later decode overwrites context-level logits. A safe
precursor therefore requires `kv_unified=true`, explicit positions/sequence IDs,
supported full-attention model families, and request-owned or immediately saved
sampling results. It is not paged attention.

Conclusion: true S4 requires a tensor-page backend or a pinned llama extension
whose attention/decode consumes Slang-supplied block tables.
