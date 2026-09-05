# Plan: context-mode / ponytail parity — phases and acceptance specs

Design: `doc/05_design/app/mcp/context_and_ponytail_parity_design.md`.
Sized for Haiku execution with Opus review: every item names the file, the
spec, and the mutation that must turn it red. Run one spec file at a time
(`bin/simple test <spec>`; ~10-15 s each on the seed).

## Phase 1 — token leaks (landed in this change, 2026-08-28)

| id | feature | code | acceptance spec | mutation-red |
|---|---|---|---|---|
| P1-1 | execute return cap 100 KB, 60/40, full output indexed as `exec:<ts>` | `main_lazy_ctx_tools.spl` `ctx_smart_truncate`, `ctx_cap_exec_stdout` | `ctx_tools_spec` "execute return cap": >100 KB stdout keeps head+tail, drops the middle marker, names `source: 'exec:`, result < 110 KB, `simple_ctx_search` finds the marker; <100 KB untouched and `chunks: 0` | set `_CTX_RETURN_CAP_BYTES` to 1 GiB -> first scenario red |
| P1-2 | query stopwords | `ctx_query_terms` | "ignores stopwords ... stopword-only query" | return `raw` unconditionally -> `the mat (1 hit(s))` red |
| P1-3 | substring fallback | `ctx_bm25_search` tail | "falls back to substring matching for a partial code token" | return `[]` instead of the fallback -> red |
| P1-4 | byte-length BM25 + prefilter | `ctx_bm25_search` | "keeps BM25 as the primary ranking with the shorter document first" + existing "linker outranks parser" | swap `dl`/`avg_len` -> order flips |
| P1-5 | Grep hint | `.claude/hooks/grep_hint.shs`, settings matcher `Grep` | `ctx_hooks_spec` "grep_hint.shs" (hint / silent on count, files_with_matches, head_limit, bad input / selftest) | drop the `count` case -> silent test red |
| P1-6 | Agent/Task routing injection + Bash upgrade | `.claude/hooks/agent_routing.shs`, `ctx_routing_block.md`, settings matcher `Agent\|Task` | `ctx_hooks_spec` "agent_routing.shs" (updatedInput carries prompt+block, `general-purpose`, other fields; Explore kept; idempotent; non-object input silent; selftest) | remove the `subagent_type` rewrite -> red |
| P1-7 | ponytail whole-message deactivation | `.claude/hooks/ponytail-prompt.shs` | hook selftest (`ponytail_spec` runs it): "Stop ponytail!" -> off, "do not stop ponytail yet" keeps ultra | revert to substring grep -> `embedded` case red |

## Phase 2 — search fidelity (next)

| id | feature | code | acceptance spec | mutation-red |
|---|---|---|---|---|
| P2-1 | in-process chunk cache keyed by store `(size, mtime)` | `_ctx_load_chunks` | `ctx_tools_spec`: two searches in one process parse the file once (count via a probe counter exported for specs); an external append invalidates | never invalidate -> second search misses the new chunk |
| P2-2 | per-source shards `chunks/<label-hash>.sdn` + index file | store layer | `source`-scoped search reads only that shard (spec asserts via `simple_ctx_doctor` row "shards"); unscoped search unions | write all to one file -> doctor row red |
| P2-3 | Porter-lite stemming (s/es/ed/ing) on both sides | `ctx_tokenize_stem` used by index and query | "linkers" finds "linker"; "running" finds "run" | stem identity -> red |
| P2-4 | Levenshtein fuzzy fallback (budget 1/2/3 by length) after substring | `ctx_bm25_search` | "lnker symbols" (typo) hits `doc:linker` with `match=fuzzy` | budget 0 -> red |
| P2-5 | before/after latency recorded with `scratchpad/ab/drive2.py` (same workload as §4 of the research doc) | doc update | numbers in `doc/10_metrics/` | — |

## Phase 3 — session persistence (C14)

| id | feature | code | acceptance spec | mutation-red |
|---|---|---|---|---|
| P3-1 | PostToolUse capture to `.simple/ctx/session/<id>.log`, 80 KB per entry | `.claude/hooks/posttool_capture.shs` | hooks spec: a 200 KB tool_result is stored as 80 KB with a truncation line; session id from hook JSON | cap removed -> size assert red |
| P3-2 | UserPromptSubmit prompt log (skips `<task-notification>` etc.) | `.claude/hooks/prompt_capture.shs` | skip list honoured; prompt stored | skip list emptied -> red |
| P3-3 | SessionStart `resume\|compact` indexes the log under `session:<id>` and emits a directive with source labels + last 5 prompts | `.claude/hooks/session_resume.shs` | directive text contains `simple_ctx_search(... source: 'session:` and the labels | no index call -> `simple_ctx_stats` chunks 0 red |
| P3-4 | 7-day sweep in `simple_ctx_upgrade` (`sweep_days` param) | `ctx_upgrade_store` | old `session:*` chunks dropped, others kept | drop nothing -> red |

## Phase 4 — ponytail companions (policy, thin)

| id | feature | code | acceptance |
|---|---|---|---|
| P4-1 | `/ponytail-review`, `/ponytail-audit`, `/ponytail-help` skills mapping onto `simple_ponytail` | `.claude/skills/ponytail-*.md` + mirrors | skill files exist, name the tool call; `ponytail_spec` asserts the mapping strings |
| P4-2 | `/ponytail-debt`: grep `(#\|//) ?ponytail:` with `no-trigger` rule | `src/lib/common/ponytail/debt.spl` + `simple_ponytail mode=debt` | marker with ceiling+upgrade listed; marker without trigger flagged; summary line `N markers, M with no trigger.` |
| P4-3 | statusline badge from `.simple/ponytail.level` | `.claude/hooks/ponytail-statusline.shs` | prints `[PONYTAIL]` / `[PONYTAIL:ULTRA]` / nothing when off |
| P4-4 | trim skill body to <= 4 KB injected at SessionStart | `.claude/skills/ponytail.md` | `wc -c` gate in ponytail_spec |

## Phase 5 — schema and removal

| id | feature | owner |
|---|---|---|
| P5-1 | `properties` for `simple_ctx_*` in `tools/list` | mcp_health lane (serializer) |
| P5-2 | remove the plugin hook lines from `~/.claude/settings.json` and uninstall `context-mode@context-mode` | user (not repo code) |
| P5-3 | re-run the 74-transcript replay after two weeks of real use and report `mcp__simple-mcp__simple_ctx_*` call counts | research doc update |

## Review checklist (Opus)

- Every landed spec ran green AND red under its named mutation.
- No new tool contract changed shape (existing `ctx_tools_spec` scenarios untouched except for added `match=` field tolerance).
- Hooks fail in the documented direction (blockers closed, hints/modify open).
- No edits to files outside `src/app/mcp`, `.claude/hooks`, `.claude/settings.json`, `test/01_unit/app/mcp`, `doc/`.
