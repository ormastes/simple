# Feature Expert: ctx_postings_purge_redaction

Term postings, explicit purge and pre-storage redaction for the repo-native
context index (`simple_ctx_*`, plan §3.4, CTX-007/008/009).

## Files
- `src/app/mcp/ctx_postings.spl` — pure inverted index + both BM25 scorers
  (`ctx_scores_by_scan` oracle, `ctx_scores_by_postings`), and the build gate
  (`ctx_postings_decide`: build after 128 cache hits of one generation).
- `src/app/mcp/ctx_retention.spl` — pure purge decision (`ctx_retention_decide`).
- `src/app/mcp/ctx_redaction.spl` — pure `ctx_redact`.
- `src/app/mcp/main_lazy_ctx_tools.spl` — `CtxIndex.postings`, `_ctx_index_with_postings_when_due`,
  `ctx_bm25_search_index_scan`, `ctx_purge_store` / `handle_simple_ctx_purge`,
  redaction call in `ctx_index_text`. Registered in `main_dispatch.spl`, `main_static_tools.spl`.
- Specs: `test/01_unit/app/mcp/ctx_{postings,retention,redaction}_spec.spl`.

## Rules
- Both scorers apply identical float ops in identical term/chunk order: parity is bit-exact.
- Purge: no selector or non-positive limit => refused; default dry run; never called from index/search.
- Redaction is rule-based, not entropy-based; hex digests are never masked. A line whose
  lowercase form changes byte length is masked whole (fail closed).

## Measured (3,700 chunks, 3.2 MB, interpreter, Windows)
Warm query scan 18/27/35 ms vs postings 7/8/9 ms; postings build 2,467 ms (hence the gate).
Redaction: 6.3 MB all-trigger-lines 802 ms; no-trigger fast path 44 ms.

## Not done
Per-goal caps / automatic retention policy; incremental postings on append; redaction of
bare high-entropy strings; purge is not lock-protected against a racing append.
