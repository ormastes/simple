# NFR Options: LLM Tooling Context/Ponytail Mimic

Date: 2026-06-25

## Option A: Small Local Tooling NFRs

- Nil-free user-visible output.
- No new raw `rt_*` shortcuts outside owner modules.
- Single-file context generation completes quickly on ordinary source files.
- Generated packs are deterministic for the same input file.
- JSON output escapes quotes, backslashes, and newlines.

Pros: Matches first implementation slice.

Cons: Does not define daemon/index performance.

Effort: Small.

## Option B: Indexed Tooling NFRs

Everything in Option A, plus:

- Index writes are append-only and bounded.
- Query latency target for local pack index.
- Explicit stale-index behavior.

Pros: Ready for context-mode-like search.

Cons: Premature if pack generation is still stubbed.

Effort: Medium.

## Recommended Selection

Option A for the first slice; add Option B when local indexing is selected.

