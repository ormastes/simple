# Context index: work remaining after the generation cache (2026-11-14)

Done: per-process generation cache (`src/app/mcp/ctx_index_cache.spl`, wired at
`main_lazy_ctx_tools.spl` `_ctx_cached_index`). Remaining, from plan 3.4/3.5:

1. Postings built at ingestion: `ctx_prepare_index` still normalises every
   chunk on the first search after any store change (2.4 s for 3000 chunks).
   Unblock: persist per-chunk term postings next to `chunks.sdn` at
   `ctx_index_text` time and extend them incrementally on append.
2. Purge / retention: `chunks.sdn` only grows; no TTL or size cap.
3. Secret redaction and path allowlist before indexing / `execute_file`.
4. Richer hit fields (line range, content digest, stale flag) in
   `ctx_format_hits`.
5. `simple context read|search|history|capture` CLI over the same store.
6. Cache keying is per process: a one-shot CLI invocation still pays the cold
   cost; item 1 is what fixes that.

Unrelated, pre-existing: `test/01_unit/app/mcp/ctx_capture_truncation_spec.spl`
fails 2/4 on untouched `origin/release/1.0.0` as well (verified by stash).
`main_lazy_ctx_tools.spl` carries 3 pre-existing `primitive_api` errors
(`ctx_run_bounded`/`ctx_execute_code` `timeout_ms`, `ctx_smart_truncate` `cap`).
