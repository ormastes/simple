# Design: context-mode / ponytail parity for the repo mimics

Research and parity matrix:
`doc/01_research/app/mcp/context_mode_ponytail_originals_vs_mimic_2026-08-28.md`.
Plan with acceptance specs: `doc/03_plan/app/mcp/context_ponytail_parity_plan.md`.

The mimics already replace both plugins for everything a model calls. This
design covers the gaps the matrix rates partial or missing, in the order that
evidence says they cost tokens, and keeps every piece pure Simple / POSIX sh
inside the existing modules (`src/app/mcp/main_lazy_ctx_tools.spl`,
`.claude/hooks/`, `src/lib/common/ponytail/`).

## D1. Execute return cap (matrix C1) — landed

Problem: `simple_ctx_execute` / `_execute_file` returned stdout in full up to
`_CTX_MAX_OUTPUT_BYTES` (1 MiB); the plugin caps at 100 KB with 60/40 smart
truncation and makes the rest searchable.

Design: `ctx_cap_exec_stdout(r)` after `ctx_run_bounded`. If
`stdout.len() > _CTX_RETURN_CAP_BYTES` (102,400): index the full stdout under
`exec:<unix_micros>`, replace it with `ctx_smart_truncate(stdout, cap, marker)`
— whole lines from the head up to 60% of the cap and from the tail up to 40%,
the marker line between them rewritten to
`[...truncated — N line(s) / M byte(s) omitted from the middle; full output
indexed as K chunk(s): simple_ctx_search(queries: [...], source: 'exec:...')]`.
Below the cap nothing is indexed (the store is reloaded on every call; growing
it for every execute would make each later call slower — see D5). Telemetry
`captured` stays the raw byte count, `returned` shrinks.

## D2. Search quality (C4) — landed (stopwords, fallback, prefilter)

- `ctx_query_terms(query)`: `ctx_tokenize` minus `_CTX_STOPWORDS` (common
  English + the plugin's dev-noise words); a query that is *only* stopwords
  keeps its raw terms so it still answers.
- Candidate prefilter: a chunk is scored only if its lowercased body contains
  some query term as a substring (a tokenized hit implies a substring hit, so
  `df` is exact). Document length is the stored byte count and `avg_len` the
  mean byte count over the source — a `# ponytail:` ceiling: scores shift
  slightly, order is preserved, and non-candidate chunks are never tokenized.
- Fallback: if BM25 yields no hit, whitespace pieces of the raw query
  (>= 3 chars, lowercased, punctuation kept) are matched as substrings and
  scored by occurrence count; hits carry `match=substring`, BM25 hits
  `match=bm25`. This is the role of the plugin's trigram table for partial
  identifiers such as `string_len` or `foo.bar`.

Not in scope (plan P2-3): Porter stemming and Levenshtein fuzzy matching, and
a title column with 2x weight (chunks have no title; the source label is the
nearest thing).

## D3. Hook parity (C12, C13, P5) — landed

- `grep_hint.shs` (PreToolUse Grep, fail-open): hint naming
  `simple_ctx_execute` / `simple_ctx_batch_execute`; silent for
  `output_mode: count | files_with_matches` or a `head_limit`.
- `agent_routing.shs` (PreToolUse `Agent|Task`, fail-open, needs `jq`):
  emits `{"hookSpecificOutput":{"hookEventName":"PreToolUse","updatedInput":
  {...tool_input, prompt: prompt + block, subagent_type: Bash -> general-purpose}}}`
  — the same envelope the plugin's `core/formatters.mjs:21-25` produces. The
  block is one file, `.claude/hooks/ctx_routing_block.md`, and the hook is
  silent when the prompt already carries `<context_window_protection>` — so
  THIS hook never stacks; the plugin's still-wired hook appends
  unconditionally (routing.mjs:184-194) until its `~/.claude/settings.json`
  lines are removed.
- `ponytail-prompt.shs`: "stop ponytail" / "normal mode" now deactivate only
  as the whole prompt (trailing punctuation ignored), mirroring
  `ponytail-config.js:40-43`; `/ponytail off` still matches anywhere.

## D4. Session persistence (C14) — designed, not built

Plugin behaviour: PostToolUse stores every tool result in a per-project
SQLite DB; PreCompact snapshots; SessionStart on `resume|compact` injects a
directive built from the stored events; a 7-day sweep on `startup`.

Repo design (no SQLite): reuse the ctx store. `posttool_capture.shs`
(PostToolUse, matcher `Bash|Read|Grep|Agent`) appends the tool result to
`.simple/ctx/session/<session_id>.log` (size-capped, 80 KB per entry like the
plugin's flush budget). `session_start.shs` (SessionStart `resume|compact`)
runs `simple_ctx_index` on that log under `session:<id>` and emits a short
directive: the last N user prompts (from a UserPromptSubmit hook) and the
ctx source labels available, so the model can `simple_ctx_search` what it
did before compaction instead of re-running it. `simple_ctx_upgrade` gains a
`--sweep 7d` that drops `session:*` chunks older than 7 days. Everything is
sh + the existing tools; the only new Simple code is the sweep.

## D5. Store cost (C3 residual) — designed, not built

`_ctx_load_chunks` parses the whole SDN store on every call; with 177 chunks a
search costs ~10-19 s in source mode on a loaded box. Design: keep the SDN file
as the durable format, add a per-process in-memory cache keyed by the store
file's `(size, mtime)` so repeated calls in one server session skip the parse;
and shard `chunks.sdn` per source label so a `source`-scoped search loads one
file. Both are behind the existing `ctx_store_dir()` and change no tool
contract.

## D6. ponytail companions (P6-P8) — policy

Thin skills `/ponytail-review` (= `simple_ponytail mode=ladder diff=...`),
`/ponytail-audit` (= `level=ultra` on a file list), `/ponytail-debt` (one
`grep -rn '# ponytail:'` with the plugin's `no-trigger` rule), `/ponytail-help`
(static). `/ponytail-gain` is intentionally not mirrored: the plugin itself
refuses to print a per-repo number, and this repo has `simple_token_stats`.
Statusline badge: optional `ponytail-statusline.shs` reading
`.simple/ponytail.level`.

## Non-goals

Replicating the plugin's `npm` self-update (`ctx_upgrade`), its 11-language
sandbox (shell / javascript / simple cover this repo), and editing the user's
`~/.claude/settings.json` (the stale plugin hook lines there are the user's to
remove).
