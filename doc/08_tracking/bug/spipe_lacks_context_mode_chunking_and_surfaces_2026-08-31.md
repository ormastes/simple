# SPipe knowledge provider lacks context-mode's chunking, stemming and exec surfaces (2026-08-31)

Status: OPEN

## Evidence

Container parity run, 20 `doc/07_guide/language/*.md` docs, 5 queries, top-10:

- context-mode 1.0.18 in `node:22-slim` — `ContentStore.searchWithFallback`
- Simple `std.common.search.query_exec.run_query_v1` in `ubuntu:24.04`

Both sides matched their host runs byte-for-byte. **Every context-mode hit appeared
in the SPipe top-10 for all 5/5 queries** — the BM25 arithmetic is at parity
(both k1=1.2 / b=0.75; SPipe's `bm25-fixed-v1` is a fixed-point contract at scale
1e6 over 5 weighted fields, FTS5 uses `bm25(chunks, 2.0, 1.0)` over 2). Rank-1
agreement was 2/5, entirely explained by the gaps below.

## Gaps

1. **No chunking (highest value).** context-mode indexes and returns *chunks* —
   `searchWithFallback("bootstrap compiler")` returned the same source three
   times, once per matching chunk. SPipe returns whole document ids, forcing the
   caller to read the entire file. This is context-mode's actual token-reduction
   mechanism, not the ranking. Needs a chunk id in the SPipe document model and a
   snippet field on `SearchHit`.
2. **No Porter stemming.** FTS5 uses `tokenize='porter unicode61'`; SPipe's
   analyzer is NFC-normalisation only, so "runtime symbols" does not match
   "symbol". Note this changes the frozen `spipe-unicode-lex-v1` analyzer
   identity — it must ship as `-v2`, never as an edit to v1.
3. **No trigram fuzzy fallback.** context-mode keeps a second `chunks_trigram`
   FTS5 table plus `fuzzyCorrect()` for typo tolerance. SPipe has no equivalent
   and fails closed on a misspelt term.
4. **No intent-gated output search.** `ctx_execute`/`ctx_execute_file` take an
   `intent` string; when output exceeds `INTENT_SEARCH_THRESHOLD` the output is
   indexed and only matching section titles + previews are returned
   (`server.ts:564 intentSearch`). SPipe has no equivalent — a large result is
   returned whole or not at all.
5. **No sandboxed execution surface.** `ctx_execute` / `ctx_execute_file` /
   `ctx_batch_execute` have no `simple_pipe` surface. Largest missing piece and
   the one with real sandbox/security design cost (`security.ts`); scope
   separately from 1-4.
6. **No savings accounting.** No `ctx_stats` equivalent.

## Already at parity

`simple_pipe` covers spipe/pipe, context, codebase, search and
ponytail/audit/simplification surfaces; `simple_context` covers index+query.

## Closed by the same change

- `/ponytail-debt` had no mimic while 148 files under `src/` carry `ponytail:`
  markers — added as `simple_ponytail` mode `debt` (alias `ledger`).
- No token-budget elision existed anywhere in the tree — added
  `std.common.token_budget.smart_truncate_bytes`, mirroring context-mode's
  `smartTruncate` 60/40 head/tail line-boundary split, and wired into the
  `simple_ponytail` response.

## Pre-existing test-tree divergence recorded at landing (required step-over record)

`sh scripts/check/check-test-tree-divergence-delta.shs <origin/main> <tip>`:
`PASS — 3202 pre-existing offender(s), 0 introduced by this range`.

The base is independently RED and was already so before this change:
`FAIL — 3953 diverged vs 965 baselined (3083 new, 95 fixed-but-still-baselined);
25 mirror-only (24 unallowlisted, 0 stale-allowlist)`. That backlog is owned
elsewhere and is not addressed here; the offender list captured at landing is
`test_tree_divergence_preexisting.txt` (untracked, regenerate with the delta
helper). This change adds `test/01_unit/lib/common/ponytail/` and
`test/01_unit/lib/common/token_budget_spec.spl` and introduces zero new
divergence.
