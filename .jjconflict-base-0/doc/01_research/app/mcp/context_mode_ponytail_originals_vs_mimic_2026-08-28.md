# context-mode and ponytail: the originals vs the repo mimics (2026-08-28)

Scope: (1) how the two user-level Claude Code plugins actually work, read from
their installed source; (2) a survey of comparable tools; (3) a feature-by-
feature evaluation of the repo mimics (`simple_ctx_*`, `simple_ponytail`, the
`.claude/hooks/*` layer, `/ponytail`) with evidence from code, the earlier
measurement lanes and this project's own transcript history; (4) verdicts.
The design and phased plan that follow from it live in
`doc/05_design/app/mcp/context_and_ponytail_parity_design.md` and
`doc/03_plan/app/mcp/context_ponytail_parity_plan.md`.

Base: `379daefd14d` (release/2026-08-27 tip). Plugin sources:
`~/.claude/plugins/cache/context-mode/context-mode/1.0.18` (npm/GitHub
`mksglu/context-mode`) and `~/.claude/plugins/cache/ponytail/ponytail/4.7.0`
(GitHub `DietrichGebert/ponytail`). Web access in this environment is
WebSearch snippets only, so every mechanism claim below is from local source,
cited `file:line`.

## 1. The originals

### 1.1 context-mode 1.0.18 — how it reduces tokens

Storage. `better-sqlite3` with FTS5. Two databases: an ephemeral sandbox DB
`<tmpdir>/context-mode-<pid>.db` (WAL; orphans of dead pids swept on the next
start), and a per-project session DB
`~/.claude/context-mode/sessions/<sha256(projectDir)[:16]>.db` with a
companion `-events.md` and a `.cleanup` flag (`hooks/session-helpers.mjs:104-133`).
Only bundles ship (`cli.bundle.mjs`, `server.bundle.mjs`); the hooks are
unbundled. (`context-mode-healed-1.0.25` is the name of a tmpdir marker file,
`hooks/pretooluse.mjs:41,45,124`, not a newer version.)

Index. Schema (server.bundle.mjs, `#k()`):

```
sources(id, label, chunk_count, code_chunk_count, indexed_at)
chunks          fts5(title, content, source_id UNINDEXED, content_type UNINDEXED, tokenize='porter unicode61')
chunks_trigram  fts5(...same..., tokenize='trigram')
vocabulary(word PRIMARY KEY)
```

Ranking `bm25(chunks, 2.0, 1.0)` (title weighted 2x), snippets via
`highlight(chunks, 1, STX, ETX)`, a ~90-word stopword strip (common English +
dev noise such as `update`, `fix`, `test`, `deps`), a fallback query builder
that requires tokens >= 3 chars, the trigram table for substring / code-token
matches, and a Levenshtein fuzzy pass with an edit budget of 1/2/3 for terms of
length <= 4 / <= 12 / longer. `LIMIT` is caller-supplied.

Execution. 11 languages; `ctx_execute_file` injects the file body into a
language variable (`FILE_CONTENT`). Output above the cap gets "smart
truncation": first 60% + last 40% of the lines (`BENCHMARK.md:79`), a hard
100 KB limit on indexed content, and the annotations
`...truncated — showing first N + last ...` / `[...truncated — use search() for
full content]`. Every execute/fetch output is auto-indexed and the tool
returns a *section digest* (title + KB per chunk); the text itself is only
reachable through `ctx_search`. Batch writes flush at most 80 KB (`h=80*1024`)
per indexed document. A global stats object tracks `calls`, `bytesReturned`,
`bytesIndexed`, `bytesSandboxed`, `sessionStart` — that is what `ctx_stats`
prints.

Hooks (`hooks/hooks.json`; the same commands are copied verbatim into the
user's `~/.claude/settings.json:20-40`, and **still fire there although
`enabledPlugins["context-mode@context-mode"]` is `false` at
`settings.json:64`** — which is why every Bash call in this repo still receives
the plugin's `<context_guidance>` block while its MCP server is not mounted):

| event | matcher | decision (`hooks/core/routing.mjs`) |
|---|---|---|
| PreToolUse | Bash | quoted content stripped (`:28-32`); `/(^|\s|&&|\||\;)(curl|wget)\s/i` (`:120`) -> **modify**: the command is *replaced* by an `echo` that tells the model to use `ctx_fetch_and_index`/`ctx_execute` and not retry (`:124`); inline HTTP `/fetch\s*\(\s*['"](https?:\/\/|http)/i`, `/requests\.(get|post|put)\s*\(/i`, `/http\.(get|request)\s*\(/i` (`:134-146`) -> modify; `/(gradlew|gradle|mvnw|mvn)\s/i` (`:150`) -> modify; **everything else -> `additionalContext: BASH_GUIDANCE`** (`:161`, text `routing-block.mjs:60`) |
| PreToolUse | Read | always `READ_GUIDANCE` (`:166`; `routing-block.mjs:56`) |
| PreToolUse | Grep | always `GREP_GUIDANCE` (`:171`; `:58`) |
| PreToolUse | WebFetch | **deny** with a reason naming `ctx_fetch_and_index` (`:175-181`) |
| PreToolUse | Agent, Task | **modify**: `ROUTING_BLOCK` (`routing-block.mjs:6-54`) appended to `tool_input.prompt`; `subagent_type == "Bash"` rewritten to `general-purpose` (`:184-194`); envelope `hookSpecificOutput.updatedInput` (`core/formatters.mjs:21-25`) |
| PreToolUse | `ctx_execute*` | only the user's Bash allow/deny globs (`:196-272`) |
| PostToolUse | all | tool results captured into the session DB |
| PreCompact | — | snapshot for the resume directive |
| UserPromptSubmit | — | prompt stored as a `user_prompt` event, skipping `<task-notification>`/`<system-reminder>`/`<context_guidance>`/`<tool-result>` (`userpromptsubmit.mjs:29-31`) |
| SessionStart | startup, compact, resume, clear | wipes sessions > 7 days, slurps `CLAUDE.md` into the DB as rule events, emits `ROUTING_BLOCK` + a session directive from `buildSessionDirective()` |

Note what the ">20 lines" rule is: **prose** inside `BASH_GUIDANCE`
(`routing-block.mjs:23`). There is no computed line estimate anywhere in the
routing code; every non-network Bash call gets the same hint.

Claimed savings (`BENCHMARK.md:9-16, 70-79, 109-125`, vendor-authored): 96%
overall (376 KB -> 16.5 KB over 21 scenarios); `ctx_execute_file`
summarisation up to 100% (315 KB -> 5.5 KB); index+search 44-93% (60.3 KB ->
11.0 KB) because search returns exact chunks; "94% more context available".

### 1.2 ponytail 4.7.0 — the skill, the levels, the hooks

Prompts and hooks only; the installed plugin declares no MCP server (a
separate optional `ponytail-mcp/` package exists). `skills/ponytail/SKILL.md`:
the ladder (`:33-38`) is YAGNI -> stdlib -> native platform feature ->
already-installed dependency -> one line -> minimum code; rules `:45-51`,
including the `ponytail:` comment convention with a named ceiling and upgrade
path (`:51`). Intensity (`:66-75`, verbatim): **lite** "Build what's asked, but
name the lazier alternative in one line. User picks." — **full** (default)
"The ladder enforced. Stdlib and native first. Shortest diff, shortest
explanation." — **ultra** "YAGNI extremist. Deletion before addition. Ship the
one-liner and challenge the rest of the requirement in the same breath."
Persistence `:25-27`: active every response; off only on "stop ponytail" /
"normal mode".

Hooks (`hooks/claude-codex-hooks.json:1-30`): SessionStart
(`startup|resume|clear|compact`) -> `hooks/ponytail-activate.js:23-78` resolves
the mode (env `PONYTAIL_DEFAULT_MODE` > `~/.config/ponytail/config.json` >
`full`, `ponytail-config.js:67-87`), writes the flag file
`~/.claude/.ponytail-active` (`ponytail-runtime.js:5-22`) and emits the
instructions (4,039 B measured by the A/B lane) plus a statusline nudge
(`:63-68`). UserPromptSubmit -> `hooks/ponytail-mode-tracker.js:8-55`: regex
`/^[/@$]ponytail/` (`:17`) parses `lite|full|ultra|off` and `/ponytail-review`;
deactivation is an **exact whole-message** match on "stop ponytail" / "normal
mode" (`ponytail-config.js:40-43`). Commands: `/ponytail` (persistent),
`/ponytail-review` (diff-scoped, `L<line>: <tag> ...`, ends `net: -N lines
possible.`), `/ponytail-audit` (repo-wide, ranked), `/ponytail-debt` (greps
`(#|//) ?ponytail:` and flags `no-trigger`), `/ponytail-gain` (static
scoreboard, never per-repo), `/ponytail-help`. Benchmark (`README.md:17-74`):
~54% less code, tokens -22%, cost -20%, time -27%, on 12 tasks against
fastapi/full-stack-fastapi-template with Haiku 4.5, n=4.

### 1.3 How comparable tools do it (WebSearch snippets)

| tool | mechanism | what it teaches |
|---|---|---|
| context-mode (mksglu) | sandbox + FTS5/BM25 retrieval; claims 98% | capture-full / index / retrieve-by-query is the core; hooks enforce routing *before* the tool runs |
| Claude Code built-ins (decodeclaude.com compaction deep-dive) | tool results over ~50,000 chars are persisted to disk with a ~2 KB preview in the transcript; 5-stage compaction (microcompact -> snip -> collapse -> auto-compact) | return a short preview plus a retrieval handle, never all-or-nothing stdout |
| MCP pagination spec | cursor pagination for `list` ops only; nothing for tool-call result size | servers must self-impose caps and offer a follow-up query |
| MCP discussion #2211 | proposal for self-imposed response caps + truncation markers + re-call with cursor | a project-level hook is the right place until MCP standardises |
| Repomix | pack a repo; `--compress` keeps Tree-sitter signatures (~70% fewer tokens); CLI + MCP | structural (AST) compression is a complementary axis to BM25-over-output |
| Context7 (Upstash) | `resolve-library-id` -> `query-docs` over a pre-indexed corpus | resolve-then-narrow-fetch idiom |
| ponytail (DietrichGebert) | session-start skill with a fixed decision ladder | a prompt-side ladder, not a context technique; measured on code size, not tokens-per-tool |

## 2. What this project's history says (74 transcripts, 20,005 tool calls)

`~/.claude/projects/-mnt-data-worktrees-simple-main/*.jsonl`, one streaming
pass (`scratchpad/parity/transcript_stats.py`): 74 sessions, 5,827 user
prompts, 20,005 `tool_use` blocks. Result bytes by tool (tokens ~ B/4):

| tool | uses | result bytes | est. tokens |
|---|---|---|---|
| Bash | 14,334 | 10,379,105 | 2.59 M |
| Agent | 2,128 | 2,249,550 | 0.56 M |
| Read | 359 | 1,363,747 | 0.34 M |
| SendMessage | 1,154 | 198,583 | 0.05 M |
| Edit / Write | 1,080 | 212,472 | 0.05 M |
| every `mcp__*` tool combined | 4 | 1,251 | 0.0003 M |

Where each mechanism would have fired:

- **Bash >20-line results:** 1,982 of 14,334 calls (13.8%) carried 5,090,704 B
  — **49% of all Bash result bytes** (p50 332 B, p90 1,741 B, p99 5,676 B,
  max 25,440 B). Had every one of those been routed through
  `simple_ctx_batch_execute` at the mimic's measured return ratio
  (883,795 -> 2,481 B; 99.7% withheld), the saving is ~1.27 M tokens over the
  74 sessions. Had they gone through `simple_ctx_execute` with the new 100 KB
  cap instead, the saving is 0 — none of these results exceeded 100 KB (the
  cap protects the tail, not the median).
- **curl/wget in Bash:** 6 commands; inline HTTP: 0; WebFetch: 0; WebSearch: 0.
  The network blockers are correct but almost never load-bearing here.
- **Read:** 359 calls, 1.36 MB; 170 of them on paths never later edited (the
  "analysis" reads the Read hint targets), 46 over 8 KB.
- **Grep tool:** 0 calls (this project's agents grep through Bash), so a Grep
  hook is parity, not savings.
- **Agent/Task:** 2,128 spawns — **the single largest mechanism the mimic
  lacked**: the plugin appends its routing block to every one; the repo relied
  on CLAUDE.md inheritance (documented as unverified in CLAUDE.md itself).
- **`mcp__*` tool results:** 4 calls in 74 sessions. Every earlier "the mimic
  saves N tokens" number was measured in a harness, never in a real session —
  the routing hooks and CLAUDE.md text had not moved real work onto the tools.
- **ponytail trigger words** in user prompts: 17 of 5,827.

Hook replay (`scratchpad/parity/hook_replay.py`): the real Bash/Read inputs
above were fed to the plugin's `pretooluse.mjs` and to the repo hooks;
agreement tables are in `scratchpad/parity/hook_replay.json` and summarised
in §3.

## 3. Parity matrix

Legend: **full** = same effect, **partial** = same intent, measurable gap,
**missing** = no repo mechanism. "Mimic (after)" marks what this change adds.

| # | feature | original mechanism | mimic mechanism (379daefd14d) | parity | evidence / after |
|---|---|---|---|---|---|
| C1 | sandboxed execute, stdout only | 11 languages; stderr dropped; 60/40 smart truncation at 100 KB; output auto-indexed; digest returned | `ctx_run_bounded` via `resource_scope` (timeout, 1 MiB cap, pid/mem caps); shell/js/simple; stderr one-line summary; **stdout returned in full up to 1 MiB** | partial -> **full** | after: `ctx_cap_exec_stdout` — 100 KB cap, 60/40 head+tail, full text indexed as `exec:<ts>`, annotation names the search source; spec "execute return cap" |
| C2 | batch execute contract | commands run, indexed (80 KB flush budget), queries answered, digest | same shape: per-command status line + BM25 hits; no flush budget (chunks are 1,200 chars each, all indexed) | full | 883,795 B -> 2,481 B measured (token-stats lane) |
| C3 | index store | SQLite FTS5, per-pid temp DB + per-project session DB | `.simple/ctx/chunks.sdn` (SDN, atomic write), persistent across processes | full (different medium) | persistence spec passes; store reload per call is O(store) — plan item |
| C4 | tokenizer / ranking | porter+unicode61 FTS5, bm25 title 2x, stopwords, trigram fallback, Levenshtein | word tokens >= 2 chars, BM25 k1=1.2 b=0.75 recomputed per query, no stopwords, no fallback | partial -> **partial+** | after: query stopwords, substring fallback (`match=substring`), byte-length normalisation + candidate prefilter; no stemming/fuzzy (plan) |
| C5 | result formatting | `highlight()` snippet, source label, title | `[rank] score= match= source= chunk= ts=` + 320-char window around first hit | full | `ctx_format_hits` |
| C6 | fetch_and_index | fetch, index, digest | capped GET (256 KB default), tags stripped, one status line | full | ctx_tools_spec |
| C7 | stats / doctor / upgrade | byte counters; doctor = shell command; upgrade = npm self-update | `simple_ctx_stats` (+ telemetry rollup), `simple_ctx_doctor` (store + hook checklist), `simple_ctx_upgrade` (schema restamp) | full (upgrade re-scoped) | VERIFY blocker 2 closed at 379daefd14d |
| C8 | curl/wget/inline-HTTP block | modify: command replaced by an echo | deny with redirect text; fail-closed | full | replay: 6 real commands, both fire |
| C9 | WebFetch | deny | deny, URL echoed, fail-closed | full | ctx_hooks_spec |
| C10 | Bash large-output hint | every non-network Bash gets BASH_GUIDANCE (prose ">20 lines") | pattern heuristic (`ctx_is_verbose && !ctx_is_bounded`), silent on bounded/short commands | partial (by design) | replay agreement in §2; the mimic is quieter, the plugin is noisier |
| C11 | Read hint | every Read | only un-windowed reads > 200 lines | partial (by design) | 359 reads, 46 > 8 KB |
| C12 | Grep hint | every Grep | none | missing -> **full** | after: `grep_hint.shs` (silent on count/files_with_matches/head_limit) |
| C13 | subagent routing injection + Bash-type upgrade | Agent/Task modify + `updatedInput` | none (CLAUDE.md inheritance only) | missing -> **full** | after: `agent_routing.shs` (jq, idempotent, fail-open), same envelope as `formatters.mjs:21-25`; 2,128 historical spawns would have been covered |
| C14 | session persistence | PostToolUse capture, PreCompact snapshot, SessionStart resume directive, 7-day sweep | none | missing | designed in the plan (phase 3); not code in this change |
| C15 | routing block at session start | SessionStart emits ROUTING_BLOCK | CLAUDE.md section (always loaded) | full | CLAUDE.md § context-mode |
| C16 | tool schema `properties` | full JSON schema per tool | `required` only (serializer owned by mcp_health lane) | partial | A/B §4.2: mimic schemas 4,532 B vs plugin 9,448 B |
| P1 | ladder + rules | SKILL.md:33-51 | `.claude/skills/ponytail.md` adapted to Simple (std over hand-rolled, gate/lint over app code, typed alias over `rt_*`) | full | ponytail_spec |
| P2 | intensity lite/full/ultra | SKILL.md:66-75 | skill table + `level` param (weight thresholds 3/2/1, `ladder.spl:19-25`) | full | |
| P3 | persistence hooks | SessionStart + UserPromptSubmit, flag file in `~/.claude` | same two hooks, `.simple/ponytail.level` | full | selftests |
| P4 | activation regex | `^[/@$]ponytail` | `/ponytail` anywhere | partial (lenient) | |
| P5 | deactivation | exact whole-message "stop ponytail" / "normal mode" | substring anywhere ("don't stop ponytail" switched it off) | partial -> **full** | after: whole-message match, selftest cases added |
| P6 | `/ponytail-review` `/ponytail-audit` | prompts | `simple_ponytail mode=ladder` on a diff / `level=ultra` on a file | partial (tool, not slash command) | |
| P7 | `/ponytail-debt` `/ponytail-gain` `/ponytail-help` | prompts | none | missing (policy/cosmetic) | debt = one grep; plan lists a thin skill |
| P8 | statusline badge | `ponytail-statusline.sh` | none | missing (cosmetic) | |
| P9 | analysis memo | none (plugin re-prompts every time) | content-hash memo keyed `(mode, level, sha256(source))` | exceeds original | 7,600 B avoided per repeat call |
| P10 | prompt-side cost | 4,039 B at SessionStart | 6,133 B | partial (costs 2 KB more per session) | A/B §3.1 |

## 4. Measurements for this change (same harness as the token-stats lane)

Harness: `scratchpad/ab/drive2.py` driving the SOURCE-mode server
(`bin/simple run src/app/mcp/main.spl`, seed binary from
`/mnt/data/worktrees/goal-bootstrap`) with a fresh `SIMPLE_CTX_DIR`, recording
`result.content[*].text` bytes (what the model receives) and latency.
Workload: `cat` of a 197,759 B / 3,944-line spec log through
`simple_ctx_batch_execute` (177 chunks), four `simple_ctx_search` calls, and
two `simple_ctx_execute` calls (197 KB and 30 KB).

### 4.1 Handler-level A/B (same 177-chunk store, same host, seed interpreter)

`probe_parity_tmp.spl` calls the handlers directly; "before" is the file at
`379daefd14d`, "after" is this change. Latency rows are single runs on a
shared box (load 20-60): treat the -41% as directional; the byte counts and
hit counts are deterministic. The E2E server stalls hit during measurement
are filed as `doc/08_tracking/bug/mcp_source_server_stalls_mid_workload_2026-08-28.md`. Store: the 197,759 B spec log indexed
as 177 chunks under `parity:big`.

| op | before | after | delta |
|---|---|---|---|
| `simple_ctx_execute` `cat` 197,759 B log | 205,224 B returned (JSON-escaped), no truncation | **106,982 B**, 60/40 truncated, full text indexed under `exec:<ts>` | **-48% bytes into context (~24.6k tokens) per >100 KB execute** |
| search, code token (`higher_layer_runtime_family`) | 2,166 B, 2,359 ms | 2,224 B, **1,397 ms** | -41% latency (candidate prefilter) |
| search, stopword phrase (`the test is in the`) | 2,165 B, 2,456 ms | 2,220 B, 2,479 ms | flat (every chunk is a candidate) |
| search, partial identifier (`layer_runtime_fam`) | 198 B, **0 hits** | 2,241 B, **5 hits**, `match=substring` | recall 0 -> 5 |

E2E (drive2.py, SOURCE-mode server): the BEFORE leg measured batch
197,759 B -> 2,159 B returned and searches at 9.6-18.9 s wall under load.
Both legs also showed the source-mode seed server stalling mid-workload on
this loaded box (BEFORE on the >100 KB execute twice, AFTER once on a search
the handler answers in 1.4 s) — an environment/server-stability fact, not a
property of either code version, and the reason the before/after evidence
above is handler-level by design.

### 4.2 Hook replay (real history through both hook stacks)

`hook_replay.py` fed the real Bash/Read tool inputs (1,982 >20-line results +
600 sampled small + all 6 curl/wget) to the plugin's `pretooluse.mjs` and the
repo hooks; `hook_replay_mimic.py` re-ran the repo side after re-tuning:

| metric | plugin | mimic before | mimic after |
|---|---|---|---|
| hint recall on the 1,982 actually->20-line results | 100% (hints on every Bash) | 2.9% (58) | **90.4% (1,792)** |
| bytes of those results covered by a hint | 5,090,704 (100%) | 240,192 (4.7%) | **4,626,856 (90.9%)** |
| hint rate on <=20-line results (noise) | 100% | 4.8% | 67.7% |
| false network denies (heredoc prose mentioning curl) | 0 (strips quotes/heredocs) | 1 | **0** |
| Read hints (150 sampled) | 150 (always) | 5 | 5 (unchanged by design: only >200-line un-windowed reads) |

Spec evidence: `ctx_tools_spec` 22/22, `ctx_hooks_spec` 20/20,
`ponytail_spec` 10/10 green; one mutated run (cap 1 GiB, fallback disabled,
stopwords disabled) turns exactly the three new tool scenarios red; hook
selftests carry their own red cases. A Simple-language gotcha found on the
way: `}}` inside a double-quoted `.spl` string literal collapses to `}`
(f-string escape), which silently truncates nested-JSON payloads in specs —
the new hook specs write `} }`.

## 5. Verdicts

**ponytail: the mimic is a proper replacement.** Ladder, levels, both hooks,
the tool, and the memo are in-repo and green; this change closes the
deactivation-matching gap (P5). Residual, all policy/cosmetic: the five
companion slash-command names (P6/P7), the statusline badge (P8), the
`^[/@$]` anchor (P4), and 2 KB more prompt-side text per session (P10).

**context-mode: a proper replacement after this change, with two residuals.**
Before it, three real gaps remained: execute output leaked up to 1 MiB into
context (C1), subagents got no routing block (C13, 2,128 historical spawns),
and search had no stopword/substring handling (C4). All three are closed here
with specs. Still open: session persistence (C14 — the plugin's PostToolUse /
PreCompact / resume-directive machinery has no repo equivalent; designed, not
built) and stemming/fuzzy matching (C4 residual). Schema `properties` (C16)
is owned by the mcp_health lane. Two facts for whoever removes the plugin:
its hooks are still hard-wired in `~/.claude/settings.json` although the
plugin is disabled, so its Agent hook keeps injecting until those lines are
removed (this change does not touch user settings; CLAUDE.md at this base is
already repointed at `simple_ctx_*`); and in 74 sessions the
repo's own `mcp__*` tools were called 4 times — routing text alone has not
moved work onto them, which is the strongest argument for the hook layer
being the mechanism that matters.
