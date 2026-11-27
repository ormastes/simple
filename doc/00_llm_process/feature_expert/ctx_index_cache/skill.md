# Feature Expert: ctx_index_cache

Per-process generation cache for the repo-native context index
(`simple_ctx_search`, `simple_ctx_batch_execute`).

## Files
- `src/app/mcp/ctx_index_cache.spl` — pure decision logic and domain types
  (`CtxStorePath`, `CtxStoreLength`, `CtxStoreDigest`, `CtxGenerationKey`,
  `CtxCacheDecision`, `CtxCacheRebuildCount`). No I/O.
- `src/app/mcp/main_lazy_ctx_tools.spl` — `_ctx_cached_index` reads the store's
  current key (exists, `file_size_signed`, `file_hash_sha256_or_empty`) BEFORE
  loading the store, asks `ctx_cache_decide`, rebuilds only on non-`Hit`.
- `test/01_unit/app/mcp/ctx_index_cache_spec.spl` — 7 examples (pure + wired).

## Rules
- Only an identical key (path, presence, length, SHA-256) is a hit. mtime is
  not part of the key (plan 3.4: advisory only).
- Present store with unusable digest => `DigestUnavailable`: never cached.
- Key is read before the store, so a racing append can only make cached chunks
  newer than their key; the next call rebuilds. Never the reverse.
- The prepared-index cache is also keyed by the `source` prefix.

## Measured (3000-chunk / ~0.4 MB store, interpreter, Windows)
search 1: 2426 ms (parse + normalise); search 2: 35 ms; search 3: 29 ms;
`ctx_index_cache_rebuilds()` stayed 1. Warm cost is dominated by the SHA-256.

## Not done
See `doc/08_tracking/bug/ctx_index_remaining_work_2026-11-14.md`.
