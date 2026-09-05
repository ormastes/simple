# TL;DR — LLM Knowledge Tooling Landscape for SPipe (2026-09-05)

Full doc: [llm_knowledge_tooling_landscape_2026-09-05.md](llm_knowledge_tooling_landscape_2026-09-05.md)

Two brief items are already built: `spipe_mcp/main.spl` (33 MCP tools) and
`fusion/graph_source.spl` (`graph-bfs-v1` BFS feeding RRF). Those become *repair*, not
*build*. With no embedding API, BM25 + proximity + the link graph is the realistic
ceiling — spend the budget there, and build the eval harness before anything it measures.

| # | Technique | Pure Simple, no network? | What SPipe would build |
|---|---|---|---|
| 1 | Chunking | Structure-aware **yes**; semantic/late/contextual **no** (need embeddings/LLM) | `scan/chunks.spl` — heading-scoped md + declaration-scoped `.spl` (cAST shape). **Skip semantic chunking** — primary evidence says it doesn't pay |
| 2 | Hybrid BM25+dense+RRF | RRF **already built**; local "embedding" **yes but not semantic** | Nothing new — `RRF_DEFAULT_K = 60` already set (`lib/common/search/fusion_types.spl:25`); just record the Cormack citation beside it. Hashed/projected vectors are an RRF decorrelator, **not** semantic recall |
| 3 | Reranking | Cross-encoder/LLM **no**; proximity **yes** | `search/rerank_sdm.spl` — proximity rescoring (**5–11% MAP documented for the PPM reverse-kernel model [P]**; SDM's own delta [U]), implemented as Metzler–Croft sequential dependence. Zero deps — best value available |
| 4 | GraphRAG | LLM extraction **no**; traversal/PPR **yes, half-built** | Seeding + decay policy for existing `build_graph_ranking`: lexical top-k as roots, `max_depth` 1–2 not 3, `seed×decay^hop`, degree cap. **No LLM entity extraction** |
| 5 | Agent memory / skills | **Yes** (except LLM-scored importance) | Two-tier disclosure: a generated *card* per doc (uid/title/desc/tags/hash) as the default load; bodies on retrieval. 1k-token card budget (Aider) |
| 6 | Context engineering | Packing/ordering/citations **yes**; LLM compaction **no** | `search/pack.spl` — MMR + knapsack to budget + **edge-placement ordering** (U-curve); emit `{uid,path,line_range,content_hash,score}` so citations re-hash offline |
| 7 | Incremental / freshness | **Yes** | ccache-shaped manifest keyed by `hash(content)`; Git racy-mtime rule as fast filter; Merkle subtree skip; tombstone+GC; **periodic full rebuild as drift backstop** (Zoekt 0.25%). Watcher optional — inotify drops events |
| 8 | Evaluation | **Yes** (LLM-judge metrics **no**) | **~50 graded queries** (TREC convention / Buckley–Voorhees), SDN gold set, recall@10 + MRR@10 + nDCG@10/@20, as a `scripts/check/` gate with PASS/FAIL/ERROR non-vacuity |
| 9 | MCP surface | **Yes — already is** | Repair: shrink **33 tools → <10**; declare+implement `resources` (currently `{"tools":[]}` only); paginate/truncate, return ids+snippets. Indexed content = untrusted input |
| +A | BM25 corpus-size limit | — | **No published threshold exists** — failure is vocabulary mismatch, not size. Cheapest local semantic signal: **RM3/Rocchio PRF → PMI co-occurrence → the link graph**. **Do not build LSA** (primary counter-evidence) |

<!-- sdn-diagram:id=spipe.knowledge_tooling.research -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spipe.knowledge_tooling.research hash=sha256:auto render=ascii
@layout dag
@direction LR

scan_chunks -> bm25_index
bm25_index -> rrf_fuse
exact_index -> rrf_fuse
graph_source -> rrf_fuse
rrf_fuse -> rerank_sdm
rerank_sdm -> pack_budget
pack_budget -> spipe_mcp
manifest_cas -> bm25_index
manifest_cas -> graph_source
eval_harness -> rrf_fuse
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spipe.knowledge_tooling.research hash=sha256:auto
# run: simple md-diagram-update
+--------------+
| scan_chunks  |--+
+--------------+  |   +-------------+
+--------------+  +-->| bm25_index  |--+
| manifest_cas |----->+-------------+  |   +-----------+   +-------------+   +-------------+   +-----------+
+--------------+  |   +-------------+  +-->| rrf_fuse  |-->| rerank_sdm  |-->| pack_budget |-->| spipe_mcp |
      |           |   | exact_index |----->+-----------+   +-------------+   +-------------+   +-----------+
      |           |   +-------------+  |         ^
      |           |   +--------------+ |   +--------------+
      +-----------+-->| graph_source |-+   | eval_harness |
                      +--------------+     +--------------+
```

</details>
<!-- sdn-diagram:end -->

Legend: `manifest_cas`, `scan_chunks`, `rerank_sdm`, `pack_budget`, `eval_harness` are new;
`bm25_index`, `exact_index`, `graph_source`, `rrf_fuse`, `spipe_mcp` exist today.
Build order: eval_harness -> graph_source policy -> rerank_sdm -> the rest.
Sourcing caveat: `simple_ctx_*` MCP tools were unavailable; all external claims came via
WebSearch snippets and carry [P]/[S]/[U] labels in the full doc.
