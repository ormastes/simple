# Append-only correction: GPU type mapper struct symbol ID layout

This correction supersedes the `lane02` accepted category row for `gpu_type_mapper_struct_symbolid_layout_2026-10-24` in `reviewed_categories.sdn`. The archived row and its original lane evidence remain intact as historical capture. Apply this later review delta when reading the checkpoint.

## Corrected classification

- Assessed source: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.
- Validity: `valid` (the original `Struct(SymbolId)` layout regression remains a valid report).
- Solution: `unknown`.
- Structural change: `unknown`.
- Action: `keep_open`.
- Reproducibility remains `untested`; all runtime qualification is still pending.
- Current `review02.csv` SHA-256: `633d7f23643a762c471e63bfc137f64ee1ebc40916d01399ead6012355d33c07`. This receipt names the row as captured after deeper consumer tracing; the full raw review CSV is not copied into this checkpoint.

## Evidence and rationale

Both mappers resolve field tables through `with_type_defs`, and CUDA installs `module.types` ([CUDA backend at the assessed source](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/plugins/backend_cuda/cuda_backend.spl#L150)). Vulkan mapper constructors/setters and compile paths omit that installation ([Vulkan mapper](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/plugins/backend_vulkan/vulkan_type_mapper.spl#L42), [Vulkan backend call paths](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/plugins/backend_vulkan/vulkan_backend.spl#L106)). Deeper caller tracing in the `review_all_02` and `fix_vulkan_type_table` reports found no active read of Vulkan's `type_mapper` field: current shader entry arguments are restricted to U32 pointers/lengths and the backend emits fixed storage/push structs ([shader compile paths](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/plugins/backend_vulkan/vulkan_backend.spl#L188), [Vulkan layout emission](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/plugins/backend_vulkan/vulkan_backend.spl#L230), [remaining Vulkan caller](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/backend/vulkan_backend.spl#L105)). Thus the missing table wiring is factual but currently has no demonstrated active layout effect. A broader structural remedy is not established; keep the bug open while identifying any real Vulkan consumer and gathering current runtime evidence.

The authored mapper tests and source repair are not runtime qualification. No live bug database/status mutation or runtime verification is represented by this correction. The archived checkpoint accounting remains 1,602 IDs, 415 accepted, 1,187 needing evidence, and 0 missing; this delta changes one accepted row's category/action and does not recompute the historical partition.
