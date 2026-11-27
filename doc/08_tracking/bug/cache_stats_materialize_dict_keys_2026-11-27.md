# Cache stats and admission materialized dictionary keys (2026-11-27)

Found by the three `test/05_perf/startup/*cardinality*` / `*key_snapshot*` contract tests
(unwired census, `unwired_shs_tests_2026-11-26.md`). Three real perf defects, all of the
`dict.keys().len()` shape that builds a full key array just to count:

- `src/lib/nogc_sync_mut/db/dbfs_engine/file_meta.spl` inode-hint admission: now `self.entries.len()`.
- `src/lib/nogc_sync_mut/src/core/decorators.spl` `cache_info()` size: now `self.cache.len()`; the
  "Dict.len() always returns -1" comment is expired (fixed natively, see `.claude/rules/code-style.md`).
- `src/compiler/90.tools/duplicate_check/cache.spl` `stats()`: one `cache_keys` snapshot reused for the
  traversal and the count (was two key materializations plus a third for the count).

Status: fixed, verification-pending (contract tests green on Linux; native Dict.len() on these
three call sites not re-run natively). Prevention: the same tests guard each pattern.
