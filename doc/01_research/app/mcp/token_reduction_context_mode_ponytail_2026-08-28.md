# Why the context-mode and ponytail mimics reduce tokens (2026-08-28)

Scope: the two repo-native MCP features that stand in for the user-level
`context-mode` plugin and the `ponytail` plugin — `simple_ctx_*`
(`src/app/mcp/main_lazy_ctx_tools.spl`) and `simple_ponytail`
(`src/app/mcp/main_lazy_query_tools.spl`) — and the telemetry that now
measures them (`src/app/mcp/main_lazy_telemetry.spl`, tool
`simple_token_stats`). Every mechanism below is named with the code that
implements it and a number measured from one real server session.

## 1. Context-mode mimic: raw output never enters the model context

A plain `Bash`/`Read` tool call returns the whole program output to the
model; every byte becomes context tokens (~4 bytes per token). The ctx tools
break that link in three places:

| Tool | What is captured (stored in the server, never returned) | What is returned to the LLM | Code |
|------|--------------------------------------------------------|------------------------------|------|
| `simple_ctx_batch_execute` | full stdout + stderr of each command, chunked (~1200 chars) into `.simple/ctx/chunks.sdn` | one status line per command + top-`limit` BM25-ranked snippets (320 chars each) for the given queries | `handle_simple_ctx_batch_execute`, `ctx_index_text`, `ctx_bm25_search`, `_ctx_snippet` |
| `simple_ctx_execute` / `_execute_file` | stdout (capped 1 MiB) + stderr | stdout only; stderr collapsed to one summary line | `ctx_run_bounded`, `_ctx_summarize_stderr` |
| `simple_ctx_fetch_and_index` | the page body (capped 256 KiB default) | one line: byte counts + chunk count; content is reachable only through `simple_ctx_search` | `handle_simple_ctx_fetch_and_index` |
| `simple_ctx_search` | nothing new | ranked chunks only (default 5, max 25) | `ctx_format_hits` |

So the model pays for ranked chunks, not for the raw dump, and pays again only
for what it explicitly searches for. The saving is inherent to the design —
the store is on disk, the search happens in the server — not a heuristic.

**Measurement (telemetry):** each `simple_ctx_*` handler now records one
ledger row `captured, returned` (`tok_record`, `TOK_FEATURE_CTX`).
`captured` is the raw byte count the tool consumed (stdout+stderr, page body,
indexed text); `returned` is the byte length of the tool result text.
`tokens_saved = max(0, captured - returned) / 4`. Rows are per call, so both
per-call and cumulative (and last-7-days) views exist.

Measured 2026-08-28, source-mode server (`bin/simple run src/app/mcp/main.spl`,
the same `main.spl` both `.mcp.json` entries are built from), one
`simple_ctx_batch_execute` running `wc -l` + `cat` over four `src/app/mcp`
files with two queries:

```
tok_events: 1, ctx, simple_ctx_batch_execute, ..., captured=140511, returned=3199, hit=0
ctx-mimic: calls=1 bytes_captured=140511 bytes_returned=3199 tokens_saved=34328
```

140,511 B in, 3,199 B out: 97.7% of the bytes stayed in the store; ~34k
tokens that a plain `cat` would have spent.

## 2. Ponytail mimic: shorter answers, and no re-analysis of unchanged files

### (a) The ladder yields a shorter answer than the source

`ponytail_ladder` / `ponytail_audit` / `ponytail_simplification_report`
(`src/app/ponytail/audit.spl`, `std.common.ponytail.ladder`) read the whole
file but return rung-tagged findings, not the file. The model asks "what is
over-engineered here?" and receives a findings list instead of reading the
source itself. Telemetry records `captured = source bytes scanned` (or the
diff length in diff mode) and `returned = findings bytes`.

Measured on `src/app/mcp/main_lazy_ctx_tools.spl` (mode `ladder`, level
`full`): `captured=35273, returned=1002` — the answer is 2.8% of the source.

### (b) Content-hash memo prevents re-analysis of unchanged files

New in this change (`handle_simple_ponytail`): in file mode the handler reads
the source, computes `key = sha256(mode + level + content)`
(`tok_memo_key`), and looks it up in `.simple/ctx/telemetry_memo.sdn`
(`tok_memo_get`). On a hit the cached findings are returned verbatim and the
ledger row carries `hit=1` with `captured = bytes of the prior analysis`
(source read + findings produced, stored at `tok_memo_put`). On a miss the
analysis runs, is recorded as (a), and is memoized before any optional
`lint: true` append. An edited file changes the hash and misses; a diff
request is one-shot and is never memoized.

"Avoided bytes" definition (a choice, stated explicitly): the second call
would otherwise re-read the source and regenerate the findings, so
`captured` on a hit is `source.len() + findings.len()` from the first run,
and `returned` is the findings again. Measured, second identical call:

```
tok_events: 2, ponytail, simple_ponytail, ..., captured=35273, returned=1002, hit=0
tok_events: 3, ponytail, simple_ponytail, ..., captured=36275, returned=1002, hit=1
ponytail-mimic: calls=2 cache_hits=1 bytes_captured=71548 bytes_returned=2004 tokens_saved=17385
```

The hit also skipped the ladder scan entirely (server-side CPU), which is
the "repeat work prevented" the memo exists for.

## 3. Reachability through both `.mcp.json` entries

`.mcp.json` declares `simple-mcp` and `simple-pipe-mcp`; both run
`bin/simple_mcp_server`, whose exec target is the native
`bin/release/<triple>/simple_mcp_server` built from `src/app/mcp/main.spl`.
Verified with `tools/list` under each client name against the source
(`SIMPLE_MCP_TOOL_SET=all bin/simple run src/app/mcp/main.spl`):

| entry | tools | `simple_token_stats` present |
|-------|-------|------------------------------|
| simple-mcp | 165 (166 at tip f92fa0bb4d5) | yes |
| simple-pipe-mcp | 165 (166 at tip f92fa0bb4d5) | yes |

The currently deployed native (`bin/release/x86_64-unknown-linux-gnu/simple_mcp_server`,
2026-08-10, 155 tools) predates the ctx tools altogether and does not serve
it; redeploy is owned by the mcp_health lane.

## 4. Grand total

Session A (four `src/app/mcp` files, above):

```
total: calls=3 bytes_captured=212059 bytes_returned=5203 tokens_saved=51713
```

Session B at tip `f92fa0bb4d5` (2026-08-28, source-mode server, one stdio
session): `simple_ctx_batch_execute` over `find src -name '*.spl' | xargs wc -l`,
`simple_ponytail` twice on `src/compiler/80.driver/driver.spl` (ladder, full),
then `simple_token_stats`:

```
tok_events: 1, ctx,      simple_ctx_batch_execute, captured=883795, returned=2481, hit=0
tok_events: 2, ponytail, simple_ponytail,          captured=7387,   returned=213,  hit=0
tok_events: 3, ponytail, simple_ponytail,          captured=7600,   returned=213,  hit=1
ctx-mimic:      calls=1 bytes_captured=883795 bytes_returned=2481 tokens_saved=220328
ponytail-mimic: calls=2 cache_hits=1 bytes_captured=14987 bytes_returned=426 tokens_saved=3639
total:          calls=3 bytes_captured=898782 bytes_returned=2907 tokens_saved=223967
```

883,795 B of `wc -l` output became 2,481 B of ranked snippets (99.7% kept
out of context); the second ponytail call hit the memo and counted the
7,387 + 213 B prior analysis as avoided. `tools/list` in that session: 166
tools, `simple_token_stats` present.

Spec: `test/01_unit/app/mcp/token_stats_spec.spl` (8 scenarios; goes red
under a wrong divisor and under a broken memo lookup). Guide:
`doc/07_guide/app/mcp/mcp.md` § Token savings.

## 5. Addendum (2026-08-28, parity lane): execute cap, search quality, hook recall

Superset study with plugin-source mechanics, a 74-transcript replay and a
parity matrix: `context_mode_ponytail_originals_vs_mimic_2026-08-28.md` (same
directory). Changes landed there that alter the numbers above:

- `simple_ctx_execute` / `_execute_file` now cap the RETURNED stdout at
  100 KB (60/40 head+tail, `ctx_smart_truncate`); the full output is indexed
  under `exec:<ts>` and the annotation names the `simple_ctx_search` source.
  Previously up to 1 MiB of stdout entered the transcript unchunked.
- `simple_ctx_search`: query-side stopwords, a substring fallback for partial
  code tokens (`match=substring` in the hit line), and BM25 over byte lengths
  with a candidate prefilter (only chunks containing a query term are
  tokenized).
- Hook-firing measured against this project's real history (74 sessions,
  14,334 Bash calls): the >20-line Bash hint's recall on the 1,982 actually-
  large results went 2.9% -> 90.4% after re-tuning (compound-statement count,
  big `sed -n`/`head`/`-A` windows, loops, per-segment verbose check);
  `bash_net_blocker` no longer denies heredocs that merely mention curl; new
  `grep_hint.shs` and `agent_routing.shs` (routing-block injection + Bash->
  general-purpose subagent upgrade, the plugin's single biggest uncovered
  mechanism here: 2,128 historical Agent spawns).
