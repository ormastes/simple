<!-- codex-design -->
# SPipe Knowledge Base — Architecture and Design (pure Simple)

**Date:** 2026-09-05  |  **Status:** Decision document — binding on the plan revision
**Plan being revised:** `doc/03_plan/infra/spipe/spipe_knowledge_compiler_refined_plan.md`
(its §3.5 hazards are binding on every decision below and are referenced, not restated)
**Evidence base (not re-derived here):** the 2026-09-05 tree audit of `src/app/spipe/`, the
2026-09-05 knowledge-surface audit, and
`doc/01_research/infra/spipe/llm_knowledge_tooling_landscape_2026-09-05.md` (confidence
labels [P]/[S]/[U] are respected: nothing below is justified by a [U] figure).
**TL;DR:** `spipe_knowledge_base_architecture_tldr.md`

Every component in this document is tagged **REUSE** (module named), **EXTEND** (module
named, what is added), or **NEW** (why nothing existing fits). Rule of the repo: reuse beats
addition; nothing speculative is designed.

---

## 0. Reconciliation with the four existing design documents

Four detail designs already sit in this directory (7,442 lines, all dated 2026-08-25).
They were written against the **JavaScript baseline** (`examples/05_stdlib/spipe/`) and
predate both the Revision-2 pure-Simple decision (2026-08-31) and PR #149 (`b657337c997`),
which landed the 2,376 lines of `scan/identity/graph/fusion/search` that actually exist.
This document is **not a fifth parallel design**; it is the reconciliation layer, and where
a decision below is already correctly made in one of the four, it defers to it by citation.

| Document | Status now | What still binds | What would mislead an implementer today |
|---|---|---|---|
| `spipe_knowledge_compiler.md` (2,800 l.) | **STILL-VALID-IN-PART** | §3 core data model (records, UIDs, edge types — ported 1:1 into `model/types.spl`); §9 rebalancing (implemented as `balance/`); §17 graph-source record + traversal (implemented as `fusion/graph_source.spl`, contract `graph-bfs-v1`) | §2 package/ownership map names `src/**.js` modules; §10 promotion/skill compilation designs LLM review, remote transfer and signed waivers — **CUT** by plan §4.1 (W2/W11) and by the research doc's "do not build" list. §5 incremental flow assumes the JS `GraphStore`; superseded by §2.4 below (ccache-shaped manifest) |
| `spipe_knowledge_compiler_search_providers.md` (2,634 l.) | **STILL-AUTHORITATIVE for the contract; superseded for the host** | §3 common search contract, §3.3 analyzer identity, §3.4 checked `bm25-fixed-v1`, **§3.5 deterministic RRF with `k = 60`**, §3.6 index semantics (create/apply/seal/snapshot), §5 cache key + content-addressed segments + write-temp/rename publication, §14 frozen identities. Decision 2 below **defers to these sections** and adds only the on-disk shape and the migration | §1 "wraps either its dependency-free JavaScript provider or a Simple provider" — there is no JS provider to wrap; `JsFixedPointSearchProvider` in §2 is a parity foil at most (plan §2.4.2). §3.1's "keep `InvertedIndex` as the small append-only positional index" is right in spirit but the tree shows it has **zero product consumers**, so the "new mutable/snapshot index" it anticipates was never built; §2.2 makes `InvertedIndex` the persisted index instead of adding a second one |
| `spipe_knowledge_compiler_cooperative_streaming.md` (1,151 l.) | **STILL-AUTHORITATIVE** (1 JS reference) | Byte-preserving deadline/cancellation for the out-of-process provider; implemented in `src/app/spipe_knowledge_provider/` (9,429 lines, `service_deadline.spl`, `work_control.spl`) | Nothing material; it already assumes the Simple provider |
| `spipe_knowledge_compiler_mcp_views.md` (857 l.) | **SUPERSEDED for the host and boundary; STILL-VALID-IN-PART for contracts** | §4 canonical URI space (`spipe://workspace/{ws}/…`), §6 the six-tool shape (`spipe_list/read/search/resolve/trace/diagnostics`) and its "tools are mandatory, resources additive" rule (the research §9 [P] evidence now backs that rule), §6.1 request limits, §11 failure behaviour | §1 calls `examples/05_stdlib/spipe/` "the authoritative SPipe package surface currently mirrored in Simple" and §2 lays out `mcp/**.js` — the live server is `src/app/spipe_mcp/main.spl` (protocol 2025-06-18, 33 tools), which this doc never mentions. §6's HTTP bearer/cookie/CSRF contract is for a transport nobody runs; **out of scope** here (no network at query time). Decision 1 replaces §1–§2 |

**Process finding (plan §1.5):** the design layer went stale unnoticed because none of the
four names a `.spl` path an agent could grep for. Every path in this document is a real
tree path as of 2026-09-05; a future audit can diff them mechanically.

---

## 1. Ground truth this design must resolve

There are **six** SPipe code locations, mutually disjoint (the brief counted five; the sixth
is load-bearing):

| # | Location | Lines | What it is | Reachable from |
|---|---|---:|---|---|
| 1 | `src/app/spipe/` | 3,952 | The knowledge compiler: 11 packages. `main.spl` dispatches only `registry` and `admit`; **7 of 11 units unreachable from any CLI**; no gate row in `config/check/must_check_gates.sdn` | nothing |
| 2 | `src/app/spipe_mcp/main.spl` | 543 | MCP server, runnable but absent from `.mcp.json` (`spipe-mcp`, protocol 2025-06-18, 33 tools = 33 dispatched). Imports `app.spipe.*` **zero** times | stdio (not in `.mcp.json`) |
| 3 | `src/lib/nogc_sync_mut/spipe/` | 1,094 | `codebase_ingest`, `hook_event`, `minimality`, `tree_context` — what #2 actually serves | #2 |
| 4 | `src/app/spipe_knowledge_provider/` | 9,429 | Persistent out-of-process lexical provider (wire, lifecycle, receipts, deadlines); `search/process_adapter.spl` in #1 already speaks to it | `bin/simple run …/main.spl` |
| 5 | `examples/05_stdlib/spipe/` | 8,649 (JS) | Frozen legacy (plan §3.2) | its own tests |
| 6 | `.spipe/spipe` | — | Older JS generation v0.1.0, separate git repo (plan debt #2) | — |

Plus the agent-facing surface that is **not** SPipe but is the closest existing KB:
`src/app/mcp/main_lazy_ctx_tools.spl` (1,181 lines) — the `simple_ctx_*` tools in the
`simple-mcp` server that `.mcp.json` actually launches and that `CLAUDE.md` routes every
agent to. It carries its own BM25 over `.simple/ctx/chunks.sdn` (schema v1: `id, source,
ts, bytes, text`), blind 1,200-char chunks, no persisted index, corpus statistics rebuilt
**per query**.

And the engine both should share: `src/lib/common/search/` — `ranking.spl`
(`bm25_fixed_v1_term_checked`, fixed-point), `inverted_index.spl` (`InvertedIndex`,
**positional** postings via `positions_in`), `snapshot.spl` (candidate → publish lifecycle),
`roaring.spl`, `top_k.spl`, `explain.spl`, `ann.spl`. Measured 2026-09-05:
`InvertedIndex` has **zero product consumers** outside its own module and spec; `index_engine_provider.spl`
(the "reusing" provider) scores by scanning every `ScopedSearchDocumentV1` per query
(`_iesp_build_corpus_facts` / `_iesp_score_document`). So the tree holds **two per-query
BM25 scanners and one unused proper index.**

The sentence this design resolves: *the knowledge compiler has no serving surface, the live
serving surface serves unrelated code, and the one persisted-capable index serves nobody.*

---

## 2. Decisions

### 2.1 Surface consolidation — one library, three thin transports, no new server

**Decision.** `src/app/spipe/` becomes the single **KB core library**, exposed through one
new facade module, and served by the transports that already exist. No third MCP server is
created. Plan debt #7 is closed by S2-W when it lands, not deferred.

| Component | Tag | Detail |
|---|---|---|
| `src/app/spipe/kb.spl` — facade | **NEW** (≈150 lines) | The *only* import a transport may take from the core: `kb_open(root) -> Result<Kb, KbError>`, `kb_search(kb, req) -> Result<KbPage, KbError>`, `kb_get(kb, uid, span?)`, `kb_cards(kb, filter)`, `kb_index(kb, mode)`, `kb_eval(kb, gold)`. Why new: three transports importing 11 packages independently is how #2 drifted to zero imports; a facade makes drift a lint hit (`use app.spipe.<anything but kb>` from a transport dir fails the wiring guard in §2.5) |
| `bin/simple knowledge <verb>` | **EXTEND** `src/app/cli/dispatch/table.spl` | One `script-tail` row → `src/app/spipe/main.spl`, exactly like the `spipe-process-harness` row (`table.spl:289`) and `spipe-docgen` (`:392`). Debt #7's "shared dispatch-table contention" no longer holds: two SPipe siblings already live in that table, and a one-row append is the smallest possible edit. Verbs: `index`, `search`, `get`, `cards`, `select`, `eval`, plus the existing `registry`, `admit`. (Plan doc says `src/app/io/dispatch/table.spl` — stale path; the table is under `src/app/cli/`) |
| `simple_ctx_*` tools (`src/app/mcp/main_lazy_ctx_tools.spl`) | **EXTEND** — re-point, keep names | Tool **names stay** (`CLAUDE.md`, `.claude/hooks/*`, and every agent prompt cite them; renaming breaks routing). Their bodies delegate to `app.spipe.kb`: `simple_ctx_search` → `kb_search`, `simple_ctx_index` → `kb_index(mode: Ingest)`, `simple_ctx_stats/doctor/upgrade` → `kb` equivalents. The exec/batch/fetch tools are untouched (sandboxing is not KB). This is the *agent-facing* surface, because `.mcp.json` launches `simple-mcp`, not `spipe-mcp` |
| `src/app/spipe_mcp/main.spl` | **EXTEND** — shrink and delegate | Keeps the transport. The arithmetic, so it can be checked: `spipe_codebase_*` (8) + `spipe_context_*` (7) + `spipe_context_sql_*` (5) = 20 tools collapse to the six-tool shape already designed in `_mcp_views.md §6` (`spipe_search/read/list/resolve/trace/diagnostics`) + `spipe_index` = 7, each taking a `backend` parameter where the old families differed only by store; the remaining 13 (`spipe_tree_*` 4, `spipe_exec_*` 3, `spipe_minimality_*` 3, `spipe_hook_*` 3) collapse to one tool per family with an `op` parameter = 4. **33 → 11 (research TLDR says "<10"; 11 is the reconciled figure).** (33 sits in the measured degradation band, research §9 [P].) Both tool tables (this and `simple_ctx_*`) call `app.spipe.kb`; they differ only in naming and audience. Audience fact: `.mcp.json` declares `simple-mcp`, `simple-lsp-mcp` and the unrelated `stitch`; `bin/spipe_mcp_server` exists as a launcher but is not declared, so today only `simple_ctx_*` is agent-facing by default |
| `src/lib/nogc_sync_mut/spipe/` | **REUSE + one boundary** | `codebase_ingest` becomes a KB *source* (its packs feed the chunker as `SourceKind.Ingested`); `hook_event`, `minimality` stay as they are (not knowledge); `tree_context.ContextStore`'s search path is retired in favour of `kb_search` — `spipe_context_put/get` keep working, `spipe_context_search` becomes a thin call. Named boundary: **lib never imports `app.spipe`**; `app.spipe.chunk` imports lib |
| `src/app/spipe_knowledge_provider/` | **REUSE** as the resident host | When a transport wants a *long-lived* index (MCP servers), `kb_open` uses `search/process_adapter.spl` → this provider, which holds the published index in memory; CLI one-shots use `search/in_process_adapter.spl`. Nothing in the provider changes for this design except that its `service.spl` loads the §2.2 index file instead of building from documents on every start. `_cooperative_streaming.md` remains authoritative for its deadline semantics |
| #5, #6 (JS) | **untouched** | Frozen (plan §3.2, debt #2) |

**Dependency direction (the named boundary):**
`lib.common.search` ← `app.spipe.{model,scan,chunk,index,graph,fusion,search}` ←
`app.spipe.kb` ← {`app.spipe.main`, `app.mcp.main_lazy_ctx_tools`, `app.spipe_mcp.main`}.
`spipe_knowledge_provider` sits beside the core (it implements `lib.common.search.provider`)
and is reached only through `search/process_adapter.spl`. No arrow points right-to-left.

### 2.2 One BM25 — `InvertedIndex` becomes the persisted index; both scanners route through it

**Decision.** The lexical index is `lib.common.search.inverted_index.InvertedIndex` +
`ranking.bm25_fixed_v1_term_checked`, persisted under `.simple/kb/`, built once per
content state, loaded once per process. `_search_providers.md §3.3–3.6, §5` are
**authoritative for the contract** (analyzer identity, checked fixed-point BM25, RRF k=60,
create/apply/seal/publish, content-addressed segments, write-temp + rename). This section
adds only what those sections left abstract: the on-disk shape, and the two migrations.

| Component | Tag | Detail |
|---|---|---|
| `InvertedIndex` | **EXTEND** `src/lib/common/search/inverted_index.spl` | (a) SDN serialisation `to_sdn_rows() / from_sdn_rows()` over its six parallel arrays (`terms`, `postings`, `all_docs`, `pos_term/pos_doc/pos_index`) — the flat-triple layout serialises as three integer columns with no nesting, which is exactly why it was chosen; (b) **`term_slot` is a linear scan over `terms`** (`inverted_index.spl:92`), O(|terms|) per lookup — at 10⁵ distinct terms that is a query-time regression, so the extension adds a sorted term table + binary search (keeps the strictly-increasing-id invariant §3.1 of `_search_providers.md` protects). Filed as a concrete perf todo, not silently absorbed |
| `index_engine_provider.spl` | **EXTEND** `src/app/spipe/search/index_engine_provider.spl` | `search()` stops calling `_iesp_build_corpus_facts` over all documents; it consults the `InvertedIndex` postings for the query terms and `corpus_stats` for N/avgdl. `explain_document` unchanged in output (the `SearchExplanation` contract is frozen, §14.14) |
| `ctx_bm25_search_index` / `ctx_bm25_search` (`main_lazy_ctx_tools.spl:512,579`) | **DELETE** after re-point | The duplicate BM25 goes; `simple_ctx_search` calls `kb_search`. Verdict text/format of the tool is preserved (agents parse it) |
| `.simple/kb/` store | **NEW** layout, **REUSE** lifecycle | Files: `manifest.sdn` (source table: `path, content_hash, bytes, mtime, size, kind`), `chunks.sdn` (§2.3 chunk records with provenance), `index.sdn` (the serialised `InvertedIndex` + `corpus_stats` rows), `graph.sdn` (edges from `scan/links.spl` via `model/edge.spl`), `cards.sdn` (§2.7). The **index id** is `sha256(canonical_bytes(sorted manifest rows) ‖ analyzer_identity ‖ score_contract ‖ chunker_version)`: same tree ⇒ byte-identical files (`model/canonical.spl` is the encoder). Publication is `snapshot.spl`'s `IndexCandidateV1 → IndexPublishRequestV1 → IndexPublishResultV1` written to `.simple/kb/<index_id>/` then `current` pointer swapped by rename — no second lifecycle |
| Migration of `.simple/ctx/` | **EXTEND** `ctx_upgrade_store` (`main_lazy_ctx_tools.spl`, `_CTX_SCHEMA_VERSION` 1→2) | Existing rows (`id, source, ts, bytes, text`) carry no path or byte range. They are re-chunked by §2.3 rules as `kind: ingested`, provenance `ctx:<source>#<id>` (citable to the ctx row, not to a file), appended to `chunks.sdn`, and `.simple/ctx/` is left in place read-only until `simple_ctx_doctor` reports zero un-migrated rows, then removed by the same tool. `simple_ctx_upgrade` already exists for exactly this schema-bump role; no new command |
| Freshness | **NEW** `src/app/spipe/index/manifest.spl` (≈200 lines) | ccache-shaped (research §7 [P]): mtime+size **fast filter** with Git's racy rule (an entry whose mtime is not strictly older than `manifest.sdn`'s own mtime is always re-hashed); re-hash via `spipe_knowledge_provider/streaming_sha256.spl` (REUSE); per-directory Merkle digest so an untouched subtree is skipped in O(1); tombstone-then-GC deletes; **unconditional full rebuild on every 400th run** (Zoekt's 0.25 %, [P]) as the drift backstop. **No file watcher** — inotify's documented failure list ([P]) makes it an optional accelerator later, never the correctness path |

Why not keep the ctx store as the index: it has no positions (the §2.4 reranker needs
`positions_in`), no term dictionary, and rescans on every query; it is a cache of text, not
an index. Why not build a new index type: `_search_providers.md §3.1` already ruled that the
positional `InvertedIndex` stays; giving it consumers is the smallest change.

### 2.3 Chunking — structure-aware, byte-addressed, corpus-tiered

**Decision.** Chunks follow document structure (cAST's shape, research §1 [P]; semantic
chunking is explicitly not built, [P] negative evidence). All boundaries are **byte
offsets** (plan §3.5.1). Chunk identity is content-addressed:
`uid = derive_canonical_uid(path, section_path, sha256(chunk_bytes))` via `model/uid.spl`.

| Component | Tag | Detail |
|---|---|---|
| `src/app/spipe/chunk/markdown.spl` | **NEW** (≈250 lines) — nothing emits heading-scoped byte ranges with a section path today | Uses `scan/headings.spl::scan_headings` (REUSE — already byte-offset) and `scan/regions.spl` (REUSE — fenced blocks never split). One chunk per heading section, `section_path = ["H1 title", "H2 title", …]`. **Size policy:** sections < 256 bytes merge into the following sibling (cAST sibling merging); sections > 4,096 bytes split at blank-line boundaries outside excluded regions, each piece keeping the same `section_path` and a `part` ordinal. Front matter and the pre-first-heading preamble form chunk 0 |
| `src/app/spipe/chunk/spl_decl.spl` | **REUSE** `compiler.frontend.treesitter.outline` (declaration outline with `Span{start, end, line, col}` from `compiler.frontend.block_types`) + **NEW** adapter (≈80 lines) | The compiler already produces per-declaration spans (`outline_members.spl:46,81` builds them with `span_new`/`merge_spans`); 89 files under `src/app/` already import `compiler.*`, so the dependency is routine. The adapter maps each top-level declaration (`fn`, `struct`, `enum`, `class`, `impl` per method, `trait`) plus its immediately preceding `#`/docstring lines to a `ByteSpan`. **One proof the spec must carry:** `Span.start/end` are asserted to be BYTE offsets by slicing the raw bytes at the span and checking they begin with the declaration keyword on a multibyte fixture (plan §3.5.1); if that assertion fails, the adapter falls back to a column-0 byte scan and a bug is filed against `Span` — no silent normalisation. A `describe`/`it` block in a `*_spec.spl` chunks per `it` |
| `src/app/spipe/chunk/sdn_record.spl` | **NEW** (≈120 lines) | One chunk per top-level key block (the `knowledge_registry.sdn` shape: `feature_routes:` list → one chunk per list item when the list exceeds 4,096 bytes, else one chunk). REUSE `std` SDN reader for the line-shape check; bytes for offsets |
| `src/app/spipe/chunk/policy.spl` | **NEW** (≈100 lines) — the corpus tiering rule | See table below. Emits `tier` and `kind` facets (`ScopedFacetV1`, REUSE) on every chunk so tiering is a query-time filter, never a separate index |

**The `doc/06_spec` problem (16,824 files / 7.49 M lines, 5–8× everything else).**
`doc/06_spec` is *generated from sspec* and mirrors `test/` paths (`.claude/rules/structure.md`:
DO NOT refactor). Indexing it as prose double-counts every spec: the `*_spec.spl` source is
the truth, the `.md` is its projection. Rule:

| Corpus | Chunk rule | Tier (default filter) |
|---|---|---|
| `test/**/*_spec.spl` | per-`it` declaration chunks | `spec` — included |
| `doc/06_spec/**/*.md` | **headings only**: one card chunk per file = H1 + first paragraph (≤ 512 bytes); body bytes are never tokenised | `spec_projection` — excluded unless `tier:spec_projection` requested |
| `doc/00_llm_process/**/skill.md`, `.claude/**/*.md` | markdown rule | `skill` — included, field weight ×1.5 on `title` (`corpus_stats.BM25_FIELD_WEIGHTS`, REUSE) |
| `doc/01–05,07` | markdown rule | `doc` — included |
| `doc/08_tracking` (4,272 files) | markdown rule | `tracking` — included |
| `doc/09_report` (3,001 files / 1.0 M lines), `doc/11_archive` | markdown rule, **H1 + H2 sections only, H3+ merged into parent** | `report` — **excluded by default**; `tier:report` opts in |
| `src/**/*.spl` (excluding vendored paths per CLAUDE.md) | declaration rule | `code` — included |
| `**/*.sdn` | record rule | `data` — included |
| `.simple/ctx` migrated rows | markdown rule over the row text | `ingested` — included |

Expected effect on the `doc/` corpus alone: tokenised content drops from ~9.9 M lines to
roughly 2.5 M (06_spec bodies and 09_report H3+ bodies removed) while every spec remains
reachable through its `.spl` source and every report through its card. `src/**` and
`test/**` add to the total on top of that and are tokenised in full (minus vendored paths).

### 2.4 Retrieval pipeline — lexical → graph → RRF → proximity rerank → budget pack

**Decision.** Five stages, all deterministic, no network, no floats in scoring (per-mille
integers throughout — plan §3.5.5 and the balance engine's int-tenths precedent).

```
query ─► analyzer (REUSE lib.common.search.analyzer, same identity as index)
      ─► S1 lexical:  BM25 over InvertedIndex top-200   (REUSE ranking.spl)  ┐
                      exact-phrase source top-50         (REUSE exact.spl)    ├─► S3 RRF fuse
      ─► S2 graph:    roots = documents of BM25 top-20;                        │   (REUSE fusion/rrf.spl,
                      build_graph_ranking depth 1 (ceiling 2, not 3)          ┘    k=60 per _search_providers §3.5)
                      score = seed_score × decay^hop, decay 500‰, fan-out cap 32/node
      ─► S4 rerank:   SDM proximity over fused top-50    (NEW search/rerank_sdm.spl)
      ─► S5 pack:     MMR + knapsack + edge placement    (NEW search/pack.spl)  ─► KbPage{hits:[Citation…]}
```

| Component | Tag | Detail |
|---|---|---|
| S1 | **REUSE** `ranking.spl`, `exact.spl`, `top_k.spl` | via the §2.2 provider |
| S2 | **EXTEND** `fusion/graph_source.spl` — policy only | The traversal (`graph-bfs-v1`, `build_graph_ranking`, `GRAPH_MAX_DEPTH_CEILING = 3`) exists and already emits a `SourceRankingV1`. Added: a `GraphSeedPolicyV1 {max_depth: 1, kb_depth_cap: 2, decay_permille: 500, fanout_cap: 32}` argument and the `seed_score × decay^hop` scoring. **`GRAPH_MAX_DEPTH_CEILING` and the `graph-bfs-v1` contract are unchanged** (two specs pin them); the KB cap of 2 lives in the policy value and is enforced before the call (research §4 [P]: uniform k-hop expansion explodes). The link graph is the strongest cheap association signal available (research §10 — authored links beat any local vector) |
| S3 | **REUSE** `fusion/rrf.spl::fuse(source_rankings, k, source_k, start_rank)` | `k` is a parameter in code, not a code default; the contract value **60** is fixed by `_search_providers.md §3.5` (line 247). `PipelineConfigV1` (NEW, data in `src/app/spipe/search/pipeline_config.spl`) pins `rrf_k: 60` and carries the Cormack 2009 citation as its comment so it is not tuned away |
| S4 | **NEW** `src/app/spipe/search/rerank_sdm.spl` (≈180 lines) | Metzler–Croft sequential dependence: `0.85·unigram + 0.10·ordered-bigram + 0.05·unordered-window(8)` over term positions from `InvertedIndex.positions_in` (this is why §2.2 keeps the positional index). Weights in per-mille (850/100/50). Nothing in the tree computes proximity; documented 5–11 % MAP [P] |
| S5 | **NEW** `src/app/spipe/search/pack.spl` (≈220 lines) | MMR selection (`λ = 700‰`, similarity = `similarity.cosine_similarity_fixed` over `similarity.build_sparse_vector` token vectors — REUSE `src/lib/common/search/similarity.spl`, fixed-point, no float), greedy fill to `budget_bytes` (default 8,192; bytes not tokens — deterministic and hazard-free), **edge placement**: rank 1 first, rank 2 last, rest in the middle (Lost-in-the-Middle U-curve, [P]). Emits `[Citation]` (§2.6) |

**Explicitly NOT in scope (research "do not build", all [P]-backed):** semantic chunking,
LSA/LSI, LLM entity extraction / GraphRAG communities, hashed pseudo-embeddings, any
`duplicate_check/ollama_client.spl` use (needs a daemon; violates no-network), a file
watcher (§2.2), personalised PageRank (only if depth-2 proves shallow **after** §2.5 can
measure it), pseudo-relevance feedback (lift is [U] this session — becomes a candidate the
day §2.5 exists to measure it).

### 2.5 Evaluation — a gate that can go red, lands first

**Decision.** The eval harness lands **before** S2-policy/S4/S5 (research §11: otherwise
their lifts are unmeasurable). It is a `scripts/check/` guard in the repo's verdict
convention, with an absolute oracle, a frozen baseline, and a sabotage self-test that runs
first and is fatal.

| Component | Tag | Detail |
|---|---|---|
| Gold set `test/fixture/spipe/kb_gold/queries.sdn` | **NEW** data | ≥ 50 hand-labelled queries (TREC convention, Buckley–Voorhees [P]). Row: `query_id, query, tier_filter, targets: [{ref, grade}]` with `grade ∈ 0..4` and `ref` = `path#section-slug` (markdown) or `path::decl_name` (`.spl`) — **document/section references, not chunk uids**, because chunk uids are content-addressed and churn on every edit while the gold must survive edits. Resolution to uids happens at eval time through `scan/headings.spl::heading_by_slug` / the decl chunker |
| `src/app/spipe/eval/metrics.spl` | **NEW** (≈150 lines) | `recall@10`, `MRR@10`, `nDCG@10`, `nDCG@20` — **all per-mille integers**. nDCG needs `1/log2(rank+1)`: a 20-entry precomputed table of `1000·1/log2(i+1)` (i = 1..20) replaces float math; IDCG is computed from the same table. This is the §3.5.5 hazard applied: no f64 ever enters a Dict or a comparison |
| `src/app/spipe/eval/run.spl` | **NEW** (≈150 lines) | Runs the pipeline with a fixed `PipelineConfigV1`, scores, emits an SDN report with per-query rows and the four aggregates |
| `scripts/check/check-kb-retrieval-eval.shs` | **NEW** guard | `--selftest` first (fatal), then the scan; verdict is the last stdout line |
| `scripts/check/kb_eval_baseline.sdn` | **NEW** baseline | Frozen `recall10, mrr10, ndcg10, ndcg20` per-mille + gold-set digest + index id |

**Exactly what makes it go red:**

| Condition | Verdict |
|---|---|
| Any aggregate falls > **10 ‰** below the baseline | `FAIL — <n> queries scored, ndcg@10 <x>‰ < baseline <y>‰ − 10` (exit 1) |
| Any aggregate rises > 10 ‰ above baseline **without** the baseline being updated in the same change | `FAIL — stale baseline` (exit 1) — the divergence-guard rule: a baseline that no longer describes the tree is how a ratchet stops ratcheting |
| A gold `ref` resolves to no chunk in the index (target rot) | `FAIL — <k> gold target(s) unresolvable: <refs>` (exit 1) |
| 0 queries scored, gold digest ≠ baseline's, no runnable `bin/simple`, or the index id in the baseline cannot be rebuilt | `ERROR — nothing was checked (<reason>)` (exit 2) — never a pass |
| `--selftest` sabotage fixtures, **phased with the stage they test** (the guard's selftest table gains a row when each lands; a fixture cannot precede its subject or the gate is ERROR from day one): at step 1 — (a) **shuffled ranking** over the gold set must score nDCG@10 < 300 ‰ and FAIL; (d) a gold set with one duplicated `query_id` must ERROR. At step 3 — (c) `--sabotage blind-chunk` (1,200-char cuts instead of §2.3) must score strictly below the structured chunker. At step 4 — (b) `--sabotage drop-graph` (S2 disabled) must score strictly below the full pipeline on the multi-hop subset (queries tagged `hop: 2`) | any sabotage that does **not** produce its expected FAIL/lower score ⇒ `ERROR — selftest` (exit 2) |
| `PASS — <n> queries scored, recall@10 <a>‰ mrr@10 <b>‰ ndcg@10 <c>‰ ndcg@20 <d>‰ (baseline <…>)`, n > 0 | exit 0 |

Gate wiring: a `push`-tier row in `config/check/must_check_gates.sdn` with
`push_blocking: false` (advisory) **until** a self-hosted `bin/simple` is deployed on push
hosts — the same honest posture `push-dual-run-shadow` took (`.claude/rules/vcs.md`); the
row and dispatch case land together so the guard is never "wired" in prose only. `--update-
baseline` exists for reviewed updates only, exactly like `--generate-baseline` elsewhere.

### 2.6 Provenance and citation — file + byte range, offline-verifiable

**Decision.** Every hit the KB returns is a `Citation` that can be verified with no index
present, by re-reading bytes and re-hashing.

```simple
struct ByteSpan:            # NEW in model/types.spl — frozen-type addition request
    path: text              # canonical POSIX path, repo-relative
    start_offset: i64       # BYTE offset, inclusive
    end_offset: i64         # BYTE offset, exclusive

struct Citation:            # NEW in model/types.spl
    chunk_uid: text         # model/uid.spl, content-addressed
    span: ByteSpan
    section_path: [text]    # markdown heading path, or [decl_name] for .spl, [] for sdn
    content_hash: text      # sha256 of exactly span's bytes at index time
    source_hash: text       # sha256 of the whole file at index time (manifest row)
    score_permille: i64     # fused, post-rerank
    rank: i64
    sources: [text]         # e.g. ["bm25", "graph"]; which S1/S2 sources contributed
    kind: text              # markdown | spl_decl | sdn_record | ingested
```

`SourceRange` (frozen, `model/types.spl:31`) is **reused unchanged** for link edges and is
**not** used as the citation span: five of its nine fields (`target_start/end`, `link_form`,
`raw_target`, `fragment`) are link-rewrite semantics with no meaning for a chunk, and
stuffing sentinel values into a frozen type is worse than one three-field struct.
`ByteSpan` is additive; no existing field moves. (Refactoring `SourceRange` to *compose*
`ByteSpan` is the tidy end state but touches a frozen shape — filed as a frozen-type
request, not done here.)

Verification (`bin/simple knowledge cite --verify <citation.sdn>`, REUSE
`streaming_sha256.spl`): re-read `[start,end)` bytes of `path`, hash, compare to
`content_hash`; if the file hash differs from `source_hash` but the span hash matches, the
citation is `Valid(moved)`; if the span hash differs, `Stale`. Stale citations carry
diagnostic **SPK550** (`citation_span_stale`), from a **new reserved block SPK550–569
"retrieval"** — the registry (`diagnostics/registry.sdn`, owner S1-D) must reserve it; the
existing free ranges (110–129 link, 510–529 balance, 530–549 admission) are all taken by
other components (plan §2.1). Every packed context block (§2.4 S5) is prefixed by its
citations, and MCP responses return `{chunk_uid, path, span, section_path, content_hash,
snippet}` — never a full body by default (research §9 repair 3, and `_mcp_views.md §6.1`).
Indexed text is untrusted: it is returned as data fields, never interpolated into tool
descriptions (tool-poisoning, [P]).

### 2.7 Progressive disclosure — cards by default, bodies on demand, pair experts automated

**Decision.** Two tiers. Tier 1 is the **card**; tier 2 is the body reached only through
`kb_get(uid, span)`. Nothing is preloaded into an agent's context by the KB itself; the
`.claude/` and `CLAUDE.md` layer stays harness-owned (audit §4: nothing reads `ref_*.md`
programmatically, and this design does not change that).

| Component | Tag | Detail |
|---|---|---|
| Card record (`cards.sdn`) | **NEW** emitter `src/app/spipe/card/emit.spl` (≈120 lines); **REUSE** `model/canonical.spl` + `model/uid.spl` for identity | `{uid, path, title, description ≤ 200 bytes (first paragraph), axis: {phase, domain, topic} (parsed from the `doc/<phase>/<domain>/<topic>/` path), tier, content_hash, byte_len}`. Emitted for every markdown document and every `skill.md`; the research's initial budget of ~1 k tokens for a card *set* (Aider repo-map default [P]) is the default `kb_cards` page size (≈ 40 cards) |
| `doc/00_llm_process/` generation | **REUSE** `src/app/llm_process_gen/main.spl` unchanged | The 168 `skill.md` files are indexed as `tier: skill` markdown like any other doc; the generator keeps writing them from `llm_process_manifest.sdn`. No skill compiler is built (plan §4.1 W2 cut stands) |
| Pair-expert selection | **EXTEND** `doc/00_llm_process/knowledge_registry.sdn`; **NEW** writer `src/app/spipe/select/pair.spl` (≈120 lines) | The routing rule already exists in data: `selection: exact-feature-then-longest-source-prefix`, `feature_routes` (feature_id → group + expert `skill.md`) and `layer_routes` (path prefix → layer group), receipt path `.spipe/<feature>/knowledge_selection.sdn`. What is missing is any **writer** — 3 of 523 lanes have a hand-authored receipt. `bin/simple knowledge select <feature_id> <paths…>` applies the rule and writes the receipt in the existing schema. **Verdict on "is pair expert cheap now": yes** — both corpora (`feature_expert/`, `layer_expert/`) and the rule exist; the cost is one 120-line writer plus one hook: when a search request carries `feature_id`, the selected pair's `skill.md` uids are added to the S2 graph **roots** (seed, not boost — the graph then pulls what those skills link to). W6 "pair experts" as designed in the research doc (handoff acceptance, SPK901/902) stays cut; this is only the selection half |

---

## 3. Component ledger

| Path | Tag | Lines (est.) |
|---|---|---:|
| `src/lib/common/search/inverted_index.spl` | EXTEND (SDN rows, sorted term table) | +150 |
| `src/app/spipe/search/index_engine_provider.spl` | EXTEND (route through `InvertedIndex`) | ±80 |
| `src/app/spipe/fusion/graph_source.spl` | EXTEND (`GraphSeedPolicyV1`, decay, fan-out cap) | +60 |
| `src/app/spipe/model/types.spl` | EXTEND (`ByteSpan`, `Citation`) — frozen-type request | +20 |
| `src/app/spipe/diagnostics/registry.sdn` | EXTEND (reserve SPK550–569) | +4 |
| `src/app/spipe/main.spl` | EXTEND (verbs `index/search/get/cards/select/eval/cite`) | +80 |
| `src/app/cli/dispatch/table.spl` | EXTEND (one `knowledge` row) | +8 |
| `src/app/mcp/main_lazy_ctx_tools.spl` | EXTEND (delegate to `kb`; delete inline BM25 and chunker) | −300 / +60 |
| `src/app/spipe_mcp/main.spl` | EXTEND (collapse 33 tools into 11; delegate) | −250 / +100 |
| `src/app/spipe/search/pipeline_config.spl` | NEW data (`PipelineConfigV1`: rrf_k 60, SDM 850/100/50, decay 500‰, λ 700‰, budget 8,192 B) | 60 |
| `doc/00_llm_process/knowledge_registry.sdn` | EXTEND (routes as needed) | data |
| `src/app/spipe/kb.spl` | NEW facade | 150 |
| `src/app/spipe/chunk/{markdown,spl_decl,sdn_record,policy}.spl` | NEW (spl_decl is an adapter over the compiler outline) | 550 |
| `src/app/spipe/index/manifest.spl` | NEW | 200 |
| `src/app/spipe/search/{rerank_sdm,pack}.spl` | NEW | 400 |
| `src/app/spipe/eval/{metrics,run}.spl` | NEW | 300 |
| `src/app/spipe/card/emit.spl`, `src/app/spipe/select/pair.spl` | NEW | 240 |
| `scripts/check/check-kb-retrieval-eval.shs`, `kb_eval_baseline.sdn`, `test/fixture/spipe/kb_gold/queries.sdn` | NEW | guard + data |
| `test/01_unit/app/spipe/{chunk_*,manifest,rerank_sdm,pack,eval_metrics,citation_verify,pair_select}_spec.spl` | NEW specs | mutation-red evidence each |

Every NEW module stays under ~250 lines (lint cost is superlinear in file content,
`.claude/rules/commands.md`).

## 4. Hazard mapping (plan §3.5 — referenced, not restated)

| §3.5 item | Where it bites here | Rule applied |
|---|---|---|
| 1 bytes vs chars | every chunker, `ByteSpan`, SDM positions, citation verify | byte iteration only; `text.len()` never paired with `s[i]`; multibyte fixtures in every chunk spec |
| 2 COW alias mutation | `InvertedIndex` build, manifest tables, graph roots | owner-mutation only; `.keys()` hoisted; `check-cow-alias-hotpath.shs` covers the new paths |
| 3 closure capture | chunk accumulators, MMR selection | explicit state structs passed/returned |
| 4 erased-receiver chains | records pulled from SDN dicts in manifest/gold loaders | bind a typed `val` before chaining |
| 5 native Dict f64 gap | scores, nDCG, decay, MMR λ | **no f64 anywhere** — per-mille `i64`, log2 table |
| 6 `Result<T,E>` only | `kb.spl` facade, manifest I/O, citation verify | `KbError` enum; `?` propagation; stale citation is a value, not an error |
| 7 seed version | `admit` verb already relies on it | unchanged |
| 9 no inheritance, `<>` | `SearchProviderAdapter` trait, `BalanceComponent` precedent | chunkers are functions over bytes returning `[ChunkRecord]`; policy is data |

## 5. Landing order (each step verifiable alone)

1. **Eval first**: gold set (≥ 50 queries), `eval/metrics.spl`, `eval/run.spl`, the guard
   with sabotage fixtures (a) and (d) only, baseline recorded against the *current*
   per-query-scan provider over whole-file documents. Nothing else may claim a lift before
   this is green-and-red-able. Fixtures (c) and (b) join at steps 3 and 4 respectively.
2. `InvertedIndex` extension + persisted `.simple/kb/` + manifest; `index_engine_provider`
   re-routed; `bin/simple knowledge index|search` row. Baseline re-recorded (should be
   equal or better; a drop is a bug).
3. Chunkers + tier policy; `simple_ctx_upgrade` v1→v2 migration; `simple_ctx_*` delegated;
   inline ctx BM25 deleted.
4. Graph seed policy (S2) → rerank (S4) → pack + citations (S5), each landing with its
   eval delta in the commit message.
5. Cards + pair-select writer; `spipe_mcp` tool collapse.
6. Gate row promoted from advisory to blocking once a self-hosted `bin/simple` exists on
   push hosts.

## 6. Recorded debt and bug records to file (not silently absorbed)

- **Bug:** `InvertedIndex.term_slot` linear scan (`inverted_index.spl:92`) — perf regression
  at repo scale; fixed in step 2.
- **Bug:** `index_engine_provider.spl` rebuilds corpus facts per query while an unused
  positional index sits beside it.
- **Debt:** `SourceRange` should compose `ByteSpan`; frozen-type request.
- **Verify-or-file:** `compiler.frontend.block_types.Span.start/end` must be proven byte
  offsets by the `spl_decl` spec's multibyte fixture; a failure files a bug against `Span`.
- **Debt:** `_mcp_views.md §1–§2` and `_search_providers.md §1` still describe a JS host;
  amend those sections to point here rather than leaving two truths.
- **Debt:** plan doc names `src/app/io/dispatch/table.spl`; the table is
  `src/app/cli/dispatch/table.spl`.
- **Reserved:** SPK550–569 (retrieval/citation) — registry row to add.
