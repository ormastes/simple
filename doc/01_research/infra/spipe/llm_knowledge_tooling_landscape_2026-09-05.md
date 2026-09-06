# LLM Knowledge Tooling Landscape — Adoptable Techniques for SPipe

**Date:** 2026-09-05  |  **Status:** Research Phase — external landscape survey
**Target system:** SPipe (project-local knowledge base + document compiler for LLM coding agents)
**In-tree snapshot reviewed:** `src/app/spipe/**`, `src/app/spipe_mcp/main.spl`, `src/app/spipe_knowledge_provider/**`, `src/lib/nogc_sync_mut/spipe/**`
**Prior art in-repo:** `doc/01_research/infra/spipe/spipe_knowledge_compiler.md` (§5 architecture, §7 LLM exposure / MCP URI space) — this document does **not** re-derive those decisions, it supplies the external evidence they were missing.
**TL;DR sibling:** `doc/01_research/infra/spipe/llm_knowledge_tooling_landscape_2026-09-05_tldr.md`

---

## User Request

> You are doing external research on the state of the art in LLM knowledge tooling, so an in-repo plan can be updated with concrete, adoptable techniques. SPipe is a project-local knowledge base + document compiler for LLM coding agents. It already has, in pure Simple: a record/identity model with content-addressed canonical hashing, markdown/SDN/sspec line-scan parsers, link extraction + a reverse (incoming-edge) index, a link-safe move/rename transaction, an advisory "balance score" over a doc tree (cohesion/trace/shape/axis dimensions), a BM25 + exact + RRF-fusion retrieval index, a diagnostics registry (SDN) and a local read-only "admission verdict" for PRs. It does NOT have: embeddings/vector search, reranking, chunking strategy, incremental/watch reindexing, an MCP server surface, graph traversal queries, citation/provenance emission, or context-window budget packing.
>
> Constraints: implementation must be pure Simple (a self-hosted language, no Python/JS deps, no external services); no network calls at query time; deterministic and content-addressed; must run in-repo on a developer machine. So "call OpenAI embeddings API" is NOT adoptable, but "how to structure hybrid lexical+semantic retrieval and what the measured lift is" IS, as is anything implementable as local code.
>
> Cover, each with: what it is, the measured/claimed benefit, whether it is implementable in pure Simple with no network, and a concrete "what SPipe would build" line: (1) chunking; (2) hybrid retrieval BM25+dense+RRF; (3) reranking; (4) GraphRAG; (5) agentic/memory systems; (6) context engineering; (7) incremental indexing/freshness; (8) evaluation; (9) MCP as a knowledge-serving surface.
>
> Prefer primary sources over listicles. Where you cite a number, cite where it came from. Where you cannot verify something, say "unverified" — do NOT invent benchmark figures.
>
> Addendum: for a corpus of roughly 10^4–10^5 markdown/code files, at what corpus size does BM25-alone measurably stop being sufficient, and what is the cheapest local (no-network, no-GPU) semantic signal that closes part of that gap?

---

## 0. Methodology and confidence labels

**Tooling note (honest).** The project's `CLAUDE.md` routes web fetches through the
`simple_ctx_fetch_and_index` / `simple_ctx_search` MCP tools. **Those tools were not
available in this session** — the `simple-mcp` server exposed only `simple_pipe` and
`simple_search`, and `simple-lsp-mcp` failed to connect. Per the task's stated fallback,
every external claim below was gathered through `WebSearch` **result snippets**, not
through fetched-and-parsed pages. This matters: a snippet can misattribute a number to
the wrong baseline. Labels are therefore applied strictly.

| Label | Meaning |
|---|---|
| **[P]** primary | The number is stated by the paper, official doc, or the vendor's own engineering post, and the URL is that source. |
| **[S]** secondary | The number originates in a primary source but reached this document via an aggregator/blog snippet; the figure is probably right, the exact scope may not be. |
| **[U]** unverified | Could not be confirmed this session. **Not to be quoted as fact.** No figure in this document was invented; anything not found is marked [U] and left blank. |

**Every "SPipe would build" line names a real module path in the current tree.** Where a
capability already exists, the line says *extend*, not *build*.

---

## 0.1 Correction to the task brief's inventory (measured in-tree, 2026-09-05)

Two items the brief lists as missing **already exist**, and the recommendations change
accordingly. This is stated up front so the plan is not written against a stale inventory.

| Brief says missing | Measured reality | Consequence |
|---|---|---|
| "an MCP server surface" | `src/app/spipe_mcp/main.spl` — 543 lines, JSON-RPC over stdio, `protocolVersion: "2025-06-18"`, `serverInfo.name = "spipe-mcp"`, **33 tools advertised in `tools/list` and all 33 dispatched** in `_dispatch_tool` (verified by set-diff: advertised 33, dispatched 33, empty difference). | §9 is "fix and shrink an existing surface", not "build one". The 33-tool count is itself the headline risk — see §9. |
| "graph traversal queries" | `src/app/spipe/fusion/graph_source.spl` — `GRAPH_SOURCE_CONTRACT = "graph-bfs-v1"`, `build_graph_ranking(edges, roots, max_depth, source_k, …)` doing a deterministic BFS over a forward adjacency index **plus** `build_reverse_index`, `GRAPH_DEFAULT_MAX_DEPTH = 3` / `GRAPH_MAX_DEPTH_CEILING = 3`, emitting a `SourceRankingV1` that feeds `fusion/rrf.spl::fuse()`. | §4 is "choose the seeding and decay policy for a traversal ranker that is already wired into RRF", not "add graph retrieval". |

Also measured: `spipe_mcp`'s `initialize` advertises `capabilities = {"tools": []}` only —
**no `resources`, no `prompts`**. That is a deliberate-looking gap and §9 addresses it.

---

## 1. Chunking strategies for code and docs

**What it is.** Splitting source documents into retrievable units. The families are
fixed-size/token windows; recursive or structure-aware splitting (respect headings,
functions, AST nodes); *semantic* chunking (place boundaries where consecutive-sentence
embedding similarity drops); *late chunking* (embed the whole document first, pool per
chunk afterwards); and *contextual retrieval* (prepend an LLM-written situating blurb to
each chunk before indexing).

**Measured benefit.**

- **Anthropic, Contextual Retrieval** — top-20 chunk **retrieval failure rate** 5.7%
  baseline → **3.7% with contextual embeddings alone (35% reduction)** → **2.9% adding
  contextual BM25 (49% reduction)** → **1.9% adding a reranker (67% reduction)**. Method:
  an LLM writes **50–100 tokens** of situating context per chunk, prepended before *both*
  embedding and BM25 indexing. One-time cost **$1.02 per million document tokens** using
  prompt caching, assuming 800-token chunks / 8k-token documents / 50-token instruction /
  100 tokens of generated context. Retrieving **20** chunks beat 5 and 10.
  [P] https://www.anthropic.com/engineering/contextual-retrieval
  **Baseline caveat:** the 5.7% figure is Anthropic's own standard-RAG baseline. It is
  **not** "BM25 alone", and must not be cited as such.
  The post gives **no prescriptive chunk-size rule** — it says size, boundary and overlap
  "can affect retrieval performance" and to experiment. Any specific "rerank top-150"
  number circulating for this post is [U].
- **Late chunking** (Günther et al., Jina AI) — nDCG@10 with 256-token fixed chunks,
  naive → late: SciFact 64.2 → 66.1, NFCorpus 23.5 → 30.0, TRECCOVID 63.4 → 64.7. Gain
  correlates with document length. [S for the table, P for the method]
  https://arxiv.org/abs/2409.04701
- **Semantic chunking does not pay.** "Is Semantic Chunking Worth the Computational
  Cost?" (Qu et al., NAACL Findings 2025) concludes the computational costs "are not
  justified by consistent performance gains" over fixed-size chunking. [P]
  https://arxiv.org/abs/2410.13070
- **Code-specific: cAST** — recursive AST splitting with sibling merging under a size
  budget gives **+4.3 Recall@5 on RepoEval** retrieval and **+2.67 Pass@1 on SWE-bench**
  vs line-based chunking. [P] https://arxiv.org/abs/2506.15655

**Pure Simple, no network?** Structure-aware chunking: **yes** — SPipe already has the
parsers (`scan/headings.spl`, `scan/regions.spl`, `scan/links.spl`). Late chunking and
semantic chunking: **no** (both require an embedding model). Contextual retrieval:
**not at query time and not offline** — it needs an LLM at *index* time. But note the
shape: it is a **deterministic, cacheable, content-addressed offline pass**, so it is the
one LLM-dependent technique that fits SPipe's architecture if an LLM is ever available in
a build step. Its output would be a prefix string stored beside the chunk, keyed by the
chunk's content hash.

**SPipe would build:** a `scan/chunks.spl` producing *heading-scoped* chunks for markdown
(section path retained as a field) and *declaration-scoped* chunks for `.spl` using the
existing region scanner — i.e. cAST's shape without an embedding model. Emit each chunk
with a stable `CanonicalField` set and derive its id via
`model/uid.spl::derive_canonical_uid`, so chunk identity is content-addressed. **Do not
build semantic chunking** — the primary evidence says it does not pay.

---

## 2. Hybrid retrieval: BM25 + dense + RRF fusion

**What it is.** Run a lexical ranker and a dense (embedding) ranker independently, then
merge the two ranked lists. Reciprocal Rank Fusion merges by rank, not score, so the
rankers need no score calibration.

**Measured benefit.**

- **RRF** (Cormack, Clarke, Büttcher, SIGIR 2009): score = Σ 1/(k + rank), with **k = 60**
  the best-average constant. RRF "consistently yields better results than any individual
  system, and better than Condorcet Fuse", and beat every previously reported LETOR 3
  method. [P] https://cormack.uwaterloo.ca/cormacksigir09-rrf.pdf
  A specific point-lift over CombMNZ is [U].
- **BEIR** (Thakur et al., NeurIPS 2021 D&B): BM25 underperforms neural rankers by
  **7–18 points in-domain on MS MARCO** yet is a **strong zero-shot baseline
  out-of-domain**, frequently beating ANCE/TAS-B under domain shift; "in-domain
  performance is not a good indicator for out-of-domain generalization." Reranking and
  late-interaction models score best zero-shot, at high compute. [P]
  https://arxiv.org/abs/2104.08663
- **Hybrid lift**: Elastic's own measurement, RRF over BM25 + ELSER on BEIR:
  **+18% average nDCG@10 over BM25 alone, +1.4% over ELSER alone**. [P for Elastic's own
  measurement] https://www.elastic.co/search-labs/blog/improving-information-retrieval-elastic-stack-hybrid
  Other circulating hybrid figures (BEIR 43.42 → 52.59, etc.) are [S] with unclear
  attribution and are **not** cited here.
- **What BM25 leaves on the table** — the vocabulary-mismatch gap, quantified: a
  "Mismatch Set" built from MS MARCO selected queries where BM25 fails to retrieve the
  gold passage in the **top-1000 of 8.84M candidates** — **988 of 6,980 dev queries
  (14.2%)**. [S] (surfaced via https://arxiv.org/pdf/2506.00041). Note the scale: 8.84M
  passages, i.e. ~10^7, two to three orders above SPipe's target corpus.

**Is a local, dependency-free "embedding" feasible — and does it buy anything?**
This is the decisive question for SPipe and the honest answer is **mostly no**.

- **Feature hashing / random projection** (Weinberger et al. 2009,
  https://arxiv.org/abs/0902.2206 [P]) gives tail bounds showing hashed **inner products**
  approximate the original bag-of-words inner products. That is *compression of the
  lexical space with added noise*. By construction it **cannot retrieve a synonym that
  BM25 missed** — the information was never there. (The math is [P]; the "therefore not
  semantic" step is reasoning, not a cited result.)
- **SimHash / MinHash** are near-duplicate and Jaccard estimators over the same lexical
  space. Useful for dedup, not for semantic recall. [definitional]
- **LSA / LSI** is the one label-free local method with genuine semantic pretension, and
  the primary evidence is **negative**: Atreya & Elkan, *"Latent Semantic Indexing (LSI)
  Fails for TREC Collections"* — after trying more LSI variants than any prior work,
  **"no way of using LSI achieves a worthwhile improvement in retrieval accuracy over
  BM25"** (TREC 2, 7, 8, 2004). [P]
  https://dl.acm.org/doi/pdf/10.1145/1964897.1964900
- **Locally-trained word vectors**: Diaz, Mitra & Craswell, *Query Expansion with
  Locally-Trained Word Embeddings* (ACL 2016) finds globally-trained embeddings
  **underperform corpus- and query-specific ones**. [P]
  https://aclanthology.org/P16-1035.pdf — **important scope caveat:** "locally trained"
  there means trained per-query on the **top-k retrieved documents**, not trained once
  over the whole repo. The lift magnitude is [U].

**Pure Simple, no network?** RRF: **already built** (`fusion/rrf.spl`). A hashed or
random-projected vector ranker: **yes, buildable** — but it should be justified as *a
decorrelated second ranker for RRF and an ANN speed-up*, **not** marketed as semantic.

**SPipe would build:** nothing new in fusion — `fusion/rrf.spl` already implements
`fuse(source_rankings, k, source_k, start_rank)` with the multi-source contract, over
`RRF_SCALE = 1e12` integer arithmetic. **Verified in-tree 2026-09-05:**
`src/lib/common/search/fusion_types.spl:25` sets `RRF_DEFAULT_K = 60` (bounds
`RRF_MIN_K = 1`, `RRF_MAX_K = 10000`, `RRF_DEFAULT_SOURCE_K = 1000`) — Cormack's constant
is already the default, so the only work is to **record the citation next to the
constant** so it is not "tuned" away by a later session. The remaining work is **adding
sources**, and the evidence says to spend that budget on §3 (proximity) and §4 (graph)
rather than on a locally-computed pseudo-embedding.

---

## 3. Reranking

**What it is.** A second, more expensive pass that rescores the top-N of a cheap first
stage. Cross-encoders jointly encode (query, passage); LLM rerankers emit a permutation.

**Measured benefit.**

- **Cross-encoder**: monoT5-3B on MS MARCO dev **MRR@10 0.398 vs BM25 0.187**
  (Expando-Mono-Duo). [P] https://arxiv.org/pdf/2101.05667. Circulating TREC-DL nDCG@10
  figures (0.573 / 0.4316 / 0.711) mix datasets and are [U] — not used.
- **RankGPT** (Sun et al., EMNLP 2023): zero-shot **listwise permutation generation** over
  a BM25 first stage with a sliding window. GPT-4 **nDCG@10 = 75.59 on TREC-DL19** [S];
  reported **+2.7 (TREC) / +2.3 (BEIR) average nDCG@10 over monoT5-3B** [S]. The BM25
  baseline value alongside these is [U]. https://arxiv.org/abs/2304.09542
- **Vendors** (Cohere Rerank 3/3.5: "up to 25% better than embedding search alone";
  "+23.4% vs hybrid, +30.8% vs BM25" on one financial dataset) are **vendor claims [S]**
  with no comparable absolute BEIR numbers published. Voyage: [U].
- **The cheap local approximation — term proximity.** This is the actionable finding.
  A proximity probabilistic model with a reverse kernel **improves BM25 by 5–11% MAP on
  TREC**. [P] https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/ppm.pdf
  The canonical framework is **Metzler & Croft's Markov Random Field / Sequential
  Dependence Model** (SIGIR 2005): score = unigrams + ordered bigrams + unordered windows,
  with typical weights around **0.85 / 0.10 / 0.05** — the *framework* is [P]
  https://ciir-publications.cs.umass.edu/getpdf.php?id=531, but **the exact weight triple
  is [S]** (0.8 / 0.1 / 0.1 also appears in the literature; confirm against the paper
  before hard-coding) and **SDM's own MAP delta is [U]**.
  Foundational: Tao & Zhai, *An Exploration of Proximity Measures in IR*, SIGIR 2007 [P].
- **Locally-trained LambdaMART LTR**: feasible in principle, but needs graded relevance
  labels, and label acquisition is the real blocker for a no-network project. [U]

**Pure Simple, no network?** Cross-encoder / LLM reranker: **no**. SDM/proximity
rescoring: **yes** — it needs only a positional postings list, which a BM25 index either
already has or can cheaply keep.

**SPipe would build:** a `search/rerank_sdm.spl` that rescores the fused top-N by **term
proximity** — documented at **5–11% MAP for the PPM reverse-kernel model [P]**, with
SDM's own delta [U] — implemented as Metzler–Croft sequential dependence over term
positions within a chunk (weights per the [S] caveat above, configurable). This is the
highest-evidence zero-dependency ranking upgrade available to SPipe.

---

## 4. GraphRAG / knowledge-graph retrieval

**What it is.** Microsoft's GraphRAG has an LLM extract an entity/relation graph from
chunks, runs **Leiden** hierarchical community detection, pre-generates community
summaries, then answers via **local search** (entity-anchored) or **global search**
(map-reduce over community summaries). It targets query-focused *summarization* /
"global sensemaking", not factoid lookup. [P] https://arxiv.org/abs/2404.16130

**Measured benefit — and what it actually beats.**

- Reported wins vs naive RAG on ~1M-token corpora, LLM-judged: **72–83% win rate on
  comprehensiveness, 62–82% on diversity**. [S] (original table in the PDF; reached here
  via snippet). Graph scale: Podcast 8,564 nodes / 20,691 edges; News 15,754 / 19,520.
  Root-level community summaries used **up to 97% fewer tokens** than source text. [S]
- **Cost.** No verified per-token dollar figure in the paper. Practitioner estimates of
  $20–50 per 1M corpus tokens with extraction ≈75% of indexing cost are **[U]** and are
  not cited as fact.
- **LazyGraphRAG** (Microsoft Research blog, Nov 2024) [P as vendor claim]: indexing cost
  **identical to vector RAG = 0.1% of full GraphRAG**, achieved by using **NLP
  noun-phrase extraction + co-occurrence instead of LLM extraction**, with no embeddings
  at index time; comparable quality to GraphRAG global search at **>700× lower query
  cost**. https://www.microsoft.com/en-us/research/blog/lazygraphrag-setting-a-new-standard-for-quality-and-cost/
- **Counter-evidence (important).** *RAG vs. GraphRAG: A Systematic Evaluation*
  (https://arxiv.org/abs/2502.11371 [P]) finds **no consistent winner**: RAG is better on
  single-hop, detail-oriented factoid queries; GraphRAG on multi-hop reasoning-intensive
  ones. **GraphRAG-Bench** (https://arxiv.org/abs/2506.05690 [P]) was built precisely
  because "GraphRAG frequently underperforms vanilla RAG on many real-world tasks."
- **The cheap graph primitive that needs no LLM: personalized PageRank.**
  **HippoRAG** (NeurIPS 2024) does multi-hop traversal in **one** retrieval step via PPR
  over a KG: **up to +20% over SOTA on multi-hop QA**, matching iterative IRCoT while
  **10–30× cheaper and 6–13× faster**. [P] https://arxiv.org/abs/2405.14831
  The classic prior art for seed-then-expand is **spreading activation** (Crestani,
  *Application of Spreading Activation Techniques in IR*, AI Review 1997 [P]).
  Known failure mode: **uniform k-hop expansion explodes** — neighbourhood growth
  approaches whole-graph enumeration within a few hops, so expansion must be gated by
  decay, per-step relevance, and degree caps. [S]

**Pure Simple, no network?** LLM entity/relation extraction and community summarization:
**no**. Leiden clustering: yes but pointless without summaries. **Seed-then-expand
traversal and PPR over an existing link graph: yes, and SPipe has already built the
traversal half.**

**SPipe would build:** *not* a new mechanism — a **seeding and decay policy** for
`fusion/graph_source.spl`. Concretely: take the lexical top-k as `roots`, run the
existing `build_graph_ranking` at **`max_depth` 1–2 rather than the ceiling of 3**, score
each visit by `seed_score × decay^hop`, cap fan-out by node degree, and feed the resulting
`SourceRankingV1` into `fusion/rrf.spl::fuse()` as a third source alongside BM25 and
exact. PPR (Bahmani et al., VLDB 2011, https://www.vldb.org/pvldb/vol4/p173-bahmani.pdf)
is the principled upgrade *if* 1–2 hops prove too shallow — not before. Explicitly **do
not** build LLM entity extraction: the counter-evidence says it would not pay for a
repo whose queries are mostly single-hop lookups, and it violates the no-network rule.

---

## 5. Agentic / memory systems: how coding agents keep project knowledge

**What it is.** Three live conventions: (a) always-loaded instruction files; (b)
on-demand skill files with progressive disclosure; (c) computed repo summaries.

**Measured/claimed benefit.**

- **Claude Code memory**: `CLAUDE.md` loaded into the system prompt at session start;
  hierarchy managed → user → project → local, concatenated, more-specific last;
  **`@path` imports are expanded inline and still count against the window** (they do not
  save context); project-root `CLAUDE.md` is re-injected after `/compact`. [P]
  https://code.claude.com/docs/en/memory
- **Agent Skills — three-tier progressive disclosure**: at startup **only the YAML
  `name` + `description`** enter context; the full `SKILL.md` body loads when the agent
  judges the skill relevant; bundled files/scripts load only during execution. [P]
  https://platform.claude.com/docs/en/agents-and-tools/agent-skills/overview
  A "median ≈80 tokens per skill discovery cost" figure circulates but is **[S]**, not
  Anthropic-authored.
- **AGENTS.md**: cross-vendor plain-Markdown convention, no required schema,
  nearest-file-wins discovery. [P] https://agents.md/. Cursor `.cursor/rules` and Copilot
  `.github/copilot-instructions.md` are the per-tool equivalents; their exact loading
  semantics are **[U]** here.
- **Aider repo map** — the closest prior art to SPipe: tree-sitter tag queries extract
  `def`/`ref` tags, build a file graph, and **personalized PageRank seeded on
  chat-relevant files** ranks what to show; rendered as elided scope-aware code under a
  **default `--map-tokens` budget of 1k tokens**, adjusted dynamically. [P]
  https://aider.chat/docs/repomap.html
- **Preload vs retrieve-on-demand.** Anthropic's position is explicit: context
  engineering is curating "the optimal set of tokens", and the recommendation is
  **just-in-time retrieval** — keep lightweight identifiers (paths, queries, links) in
  context and load data at runtime via tools, because there is no stale index, disclosure
  is progressive, and metadata (names, folders, timestamps) is itself a relevance signal.
  [P as stated position, **not** as a measurement]
  https://www.anthropic.com/engineering/effective-context-engineering-for-ai-agents
  The widely-repeated claim that the Claude Code team tried vector DBs and "grep won" is
  **[U] — every source located is a blog** and it is not cited here as fact.
- **Evidence that preloading has a ceiling** — Databricks, *Long Context RAG Performance
  of LLMs* (https://arxiv.org/pdf/2411.03538 [P]): 20 models, context 2k→128k.
  **Llama 3.1 405B degrades after 32k; GPT-4-0125-preview after 64k.** Distinct failure
  modes, not graceful decay: **Claude 3.5 copyright-refusals 3.7% @16k → 49.5% @64k**;
  **DBRX instruction-following failures 5.2% @8k → 50.4% @32k**.
- **Memory-system research**: MemGPT/Letta's OS-style paging with recall + archival stores
  [P mechanism, https://arxiv.org/abs/2310.08560, accuracy deltas [U]]; Generative Agents'
  **recency (exponential decay) + importance (LLM score) + relevance (cosine)** retrieval
  scoring [P mechanism, https://arxiv.org/abs/2304.03442, ablation numbers [U]]; **Mem0**
  claims **+26% relative** LLM-judge score vs built-in memory, **~91% lower p95 latency**,
  **~90% token-cost reduction vs full context** [P as the paper's self-reported claim;
  the LOCOMO benchmark has since been criticised] https://arxiv.org/abs/2504.19413;
  **A-MEM** claims up to **6× ROUGE-L on multi-hop** and **85–93% fewer memory-operation
  tokens** [P claim / S extraction] https://arxiv.org/abs/2502.12110.

**Pure Simple, no network?** All of it, except the LLM-scored "importance" dimension of
Generative Agents. Progressive disclosure is a *file-layout and index* discipline, not a
model capability.

**SPipe would build:** a **two-tier disclosure contract** over the doc tree, mirroring
Agent Skills: every SPipe document emits a machine-generated *card* (uid, title, one-line
description, axis tags, content hash) and the card set is what an agent loads by default;
bodies load only through a retrieval call. The card is a natural output of the existing
`model/canonical.spl` + `model/uid.spl` pair. Take the **1k-token budget** from Aider's
repo map as the initial card-set budget, and take **PPR-seeded ranking** as the selection
rule (§4) rather than alphabetical or path order.

---

## 6. Context engineering: budget packing, ordering, compaction, provenance

**What it is.** Deciding *which* retrieved units enter the window, in what order, at what
fidelity, and with what attribution.

**Measured benefit.**

- **Lost in the Middle** (Liu et al., TACL 2024): with the relevant document shuffled to
  positions 1/5/10/15/20 of 20, performance follows a **U-shaped curve** — best when
  first, near-best when last, **worst mid-context**. Reported drop **~20–30 points**
  (secondary summaries say 15–25, so treat the magnitude as approximate). Notably,
  worst-case mid-context accuracy can fall **below the model's closed-book accuracy**.
  [P for the paper and the U-shape; the exact per-model delta is [S]]
  https://arxiv.org/abs/2307.03172
- **RULER** (https://arxiv.org/abs/2404.06654 [P]): 17 long-context models, 13 synthetic
  tasks at 4k→128k. Models are near-perfect on vanilla needle-in-a-haystack but drop
  substantially as length grows — **claimed context windows far exceed effective
  length**. The per-model effective-length table was **not retrieved [U]**.
- **Chroma, "Context Rot"** (https://www.trychroma.com/research/context-rot): **all 18
  frontier models tested degrade with length**; degradation is **non-uniform (cliffs, not
  slopes)**; it worsens as **needle–question semantic similarity falls**; and
  counterintuitively **shuffled haystacks beat logically coherent ones across all 18
  models**. The circulating "~30 pt" and "7.9%" figures reached this document via
  secondary summary — **[S], confirm in the report before quoting**.
- **Budget packing / ordering prior art**: **MMR** (Carbonell & Goldstein, SIGIR 1998) —
  greedily select to maximise `λ·relevance − (1−λ)·max_similarity_to_already_selected`,
  shown clearly superior for non-redundant multi-document summaries. [P]
  https://dl.acm.org/doi/10.1145/290941.291025. Knapsack-style token-budget selection and
  **edge-placement ordering** (best passages first and last, mirroring the U-curve) are
  engineering practice derived from Lost-in-the-Middle with **no single canonical
  citation [U]**.
- **Compaction**: summarise a near-full window and reinitiate from the summary,
  preserving architectural decisions, unresolved bugs, implementation details. [P]
  https://platform.claude.com/docs/en/build-with-claude/compaction
- **LLMLingua** (EMNLP 2023): **up to 20× prompt compression with ≤1.5 pt performance
  drop**; on GSM8K exact-match falls **1.44 pts @14×** and **1.52 pts @20×**. [P]
  https://arxiv.org/abs/2310.05736
- **Citation / provenance**: **ALCE** (Gao et al., EMNLP 2023) is the reference benchmark
  for verifiable generation — inline citations to retrieved passage IDs, scored by
  **citation recall** (is the statement entailed by its cited passages) and **citation
  precision** (is each citation necessary), via NLI. [P] https://arxiv.org/abs/2305.14627.
  Positional refinement: ALiiCE, https://arxiv.org/abs/2406.13375. The specific
  "85.1% / 77.6% human agreement" pair attributed to these metrics is **[U]** — likely a
  system score, not a metric-validation figure. The engineering practice of stable IDs +
  line ranges + content hashes as the citation contract has **no primary citation [U]**,
  but it is exactly what ALCE's metrics require in order to be computable.

**Pure Simple, no network?** MMR selection, knapsack packing, U-curve-aware ordering, and
citation emission: **all yes** — they are arithmetic over an already-computed ranking.
LLM-based compaction and NLI-scored citation metrics: **no**.

**SPipe would build:** a `search/pack.spl` that takes the fused ranking plus a token
budget and returns an ordered, deduplicated context block: MMR selection for diversity
(λ configurable, default documented), greedy knapsack fill to the budget, and
**edge-placement ordering** — highest-scoring unit first, second-highest **last**,
mid-ranked in the middle. Every emitted unit carries `{uid, path, line_range,
content_hash, score, source}` so a citation is verifiable offline by re-hashing —
`model/canonical.spl::canonical_bytes` already provides the hash primitive. This makes
SPipe's output *checkable*, which is the property the repo's admission/verdict culture
already values.

---

## 7. Incremental indexing and freshness

**What it is.** Keeping the index consistent with a mutating working tree without a full
rebuild, and knowing when it is *not*.

**Prior art worth copying.**

- **Lucene's immutable-segment model.** Segments are immutable; adds create new segments,
  deletes/updates are tombstones in a `.liv` bitmap, physically removed only at merge
  (default `TieredMergePolicy`). Near-real-time search comes from
  `DirectoryReader.open(IndexWriter)`, which makes a flushed segment searchable **without
  a commit/fsync**. Elasticsearch's `index.refresh_interval` default is **1s** (5s on
  Elastic Cloud Serverless), and refresh is **skipped on indices with no search in the
  last 30s** — i.e. freshness work is demand-driven. [P]
  https://www.elastic.co/docs/manage-data/data-store/near-real-time-search
  Tantivy has the same shape (`Segment` atomic unit, `commit()` publishes, background
  merges under a `MergePolicy`) [P, https://github.com/quickwit-oss/tantivy/blob/main/ARCHITECTURE.md];
  its freshness latency is **[U]**.
- **Zoekt (Google → Sourcegraph)**, the closest code-search analogue: trigram index whose
  "construction is straightforward, and can easily be made incremental"; positional
  trigrams need ≈**1.2× corpus size** in RAM. [P]
  https://github.com/sourcegraph/zoekt/blob/main/doc/design.md
  **The lesson worth stealing:** Sourcegraph's indexserver deliberately **force-reindexes
  at a default 0.25% probability per cycle** rather than trusting incremental state
  indefinitely — a periodic full rebuild as a correctness backstop against incremental
  drift. [P, zoekt `cmd/zoekt-sourcegraph-indexserver/main.go`]
- **GitHub "Blackbird"** for scale context: 45M repos, 115 TB of code, 15.5B documents,
  deduped to ~28 TB, final index 25 TB; ingest ~**120,000 documents/second**, serving
  ~**640 queries/sec** (vs ~0.01 q/s for ripgrep on the same corpus). [P]
  https://github.blog/engineering/architecture-optimization/the-technology-behind-githubs-new-code-search/
- **Content-addressed invalidation — the build-system canon.** Bazel's remote cache is an
  **action cache** (action hash → ActionResult, `/ac/`) over a **content-addressable
  store** (`/cas/`), action key = digest of metadata + inputs, **SHA-256 by default** [P,
  https://bazel.build/remote/caching]. Buck2 hashes command + all inputs with the input
  root as an **REv2 Merkle-tree digest** [P, https://buck2.build/docs/users/remote_execution/].
  Nix distinguishes input-addressed (hash of the derivation graph) from content-addressed
  outputs [P, https://nix.dev/manual/nix/2.28/store/derivation/outputs/content-address.html].
  **ccache direct mode is the closest analogue to a document index**: a *manifest* records
  which include files a compilation actually read, and lookup re-hashes their *current*
  contents — with the documented gap that a header which *would* have been used had it
  existed is not recorded. [P] https://ccache.dev/manual/4.13.6.html
  **Transferable principle** (synthesis, not a citation): key index entries by
  `hash(content)`, never `path + mtime`. Then identical bytes are never re-indexed
  regardless of path or mtime churn; a rename is a metadata-only edge update; a
  Merkle/tree hash over a directory proves a subtree unchanged in O(1) and skips it
  (exactly Git's tree objects); and deletion becomes tombstone + GC because content may
  still be referenced elsewhere.
- **Watch-based reindex — the failure modes are severe and documented.** [P]
  https://man7.org/linux/man-pages/man7/inotify.7.html: default
  `fs.inotify.max_user_watches` commonly **8192**, ~**1 kB unswappable kernel memory per
  watch**, one watch per directory for recursive watching, and directories past the limit
  are **silently never watched**; the queue can **overflow**, losing events with a single
  `IN_Q_OVERFLOW`; `IN_MOVED_FROM`/`IN_MOVED_TO` are **not atomically paired** — which is
  precisely the editor "write temp file, atomic rename" pattern; new subdirectories race
  the watch installation; and no events are reported for network filesystems.
  **Watchman**'s answer: per-query **cookie files** give the guarantee "everything before
  this query is observed", and desync recovery is a **recursive recrawl** that marks all
  files changed — which Watchman's own docs call undesirable and expensive. Debouncing is
  the `settle` option. [P] https://facebook.github.io/watchman/docs/cookies
- **Staleness without a watcher — the canonical writeup is Git's "racy-git".** mtime
  typically has 1-second resolution, so a write in the same second as an index update
  leaves cached stat data matching while content differs. Git treats any entry whose mtime
  is **not strictly older than the index file's own mtime** as "racily clean", re-reads
  and re-hashes it, and truncates cached `st_size` to zero when rewriting the index to
  force a later recheck. [P] https://git-scm.com/docs/racy-git
  **Therefore mtime+size is a fast filter, never proof.** Clock-skew and
  checkout-resets-mtime guidance: **[U]**, no primary source found.

**Pure Simple, no network?** All of it. Content-addressed invalidation is arithmetic and
file I/O. A watcher is optional — and given the inotify failure list, *should* be
optional.

**SPipe would build:** a **ccache-shaped manifest**, not a watcher-first design.
Each index entry records the set of `(source_path, content_hash)` it was derived from;
validation re-hashes those paths and compares. SPipe already has the primitives —
`model/canonical.spl::canonical_bytes` and
`spipe_knowledge_provider/streaming_sha256.spl`. Layer it: (1) an mtime+size **fast
filter** to decide what to hash, with Git's racy rule applied (an entry whose mtime is not
strictly older than the manifest's own mtime is always re-hashed); (2) a Merkle tree hash
per directory so an untouched subtree is skipped in O(1); (3) tombstone-plus-GC deletes
rather than in-place removal, matching Lucene's segment discipline; (4) **a periodic
unconditional full rebuild** as the drift backstop, taking Zoekt's 0.25%-per-cycle idea
directly. A file watcher is a *later, optional* accelerator, and if built must treat
`IN_Q_OVERFLOW` and any move event as "recrawl this subtree", never as a precise delta.

---

## 8. Evaluation: is the knowledge base actually helping?

**What it is.** Offline retrieval metrics, RAG-specific answer metrics, and
task-level outcome metrics — three different questions, often conflated.

**Measured benefit / established practice.**

- **Classic IR**: recall@k, MRR@k, nDCG@k. TREC 2024 RAG used **0–4 graded relevance**
  and reported **nDCG@20, nDCG@100, Recall@100** over **301 topics** on MS MARCO V2.1
  (113,520,750 segments). [P] https://arxiv.org/abs/2411.08275 ·
  https://trec-rag.github.io/annoucements/evaluation/
  **Pitfall — shallow pooling:** only pooled documents are judged and unjudged documents
  are scored non-relevant, systematically penalising systems that retrieve outside the
  pool. BEIR quantifies this as *Hole@10*: **ANCE 14.4%, TAS-B 31.8%** of returned hits
  unjudged. [P] https://arxiv.org/abs/2104.08663
- **RAG-specific**: **RAGAS** — reference-free faithfulness / answer relevance / context
  relevance, decomposing answers into atomic claims and entailment-checking against
  context; **requires an LLM judge**. [P] https://arxiv.org/abs/2309.15217.
  **ARES** does the same three dimensions but with **lightweight LM judges fine-tuned on
  synthetic data plus prediction-powered inference over a few hundred human
  annotations**. [P] https://arxiv.org/abs/2311.09476
- **Retrieval → agent task success.** SWE-bench (original paper): with BM25 retrieval at a
  27k-token limit, **~40% of instances get a superset of the oracle files, but nearly half
  get none of them** — a directly measured retrieval ceiling on patch success. [P]
  https://arxiv.org/pdf/2310.06770. File-level localization Acc@5 comparisons (BM25 <10%,
  Agentless ~23.9%) are **[S]**, and **no clean isolated ablation proving the causal link
  retrieval-quality → task-success was found — treat the causal claim as [U]**.
- **LLM-as-judge reliability**: MT-Bench / Chatbot Arena reports GPT-4 at **>80%
  agreement with humans (~85%)**, *exceeding human–human agreement (~81%)*, while
  explicitly characterising **position, verbosity and self-enhancement biases**. [P]
  https://arxiv.org/abs/2306.05685. Per-bias magnitudes are [U].
- **How many queries are enough** — the number SPipe actually needs: Buckley & Voorhees,
  *The effect of topic set size on retrieval experiment error* (SIGIR 2002) — error rate
  falls with topic count, **25–50 queries give usable confidence**, and **TREC's
  convention is 50 topics**. [P] https://dl.acm.org/doi/10.1145/564376.564432 ·
  follow-up Sakai, *Topic set size redux* (SIGIR 2009)
  https://dl.acm.org/doi/10.1145/1571941.1572138

**Pure Simple, no network?** recall@k / MRR / nDCG over a hand-labelled query set:
**yes, trivially, and deterministically**. RAGAS/ARES-style answer metrics: **no** (LLM
judge). Task-level metrics: out of scope for an in-repo knowledge base.

**SPipe would build:** the cheapest honest harness is **~50 hand-labelled queries with
graded (0–4) gold document sets**, stored as SDN beside the diagnostics registry, scored
deterministically with **recall@10, MRR@10, nDCG@10 and nDCG@20** (both cutoffs, so a
shallow-pool artifact is visible). Fifty is not a guess — it is TREC's convention and the
Buckley–Voorhees stability result. Wire it as a `scripts/check/` gate with the repo's
standard verdict convention (`PASS — <n> queries scored, nDCG@10 = …` / `FAIL` /
`ERROR — nothing was checked`, where a 0-query run is ERROR, never a pass), matching
`.claude/rules/vcs.md`'s non-vacuity discipline. Gold labels are the *only* expensive
input, and 50 queries is a bounded, one-time human cost.

---

## 9. MCP as a knowledge-serving surface

**What it is.** MCP defines three server primitives, distinguished by *who decides when
they are used* — this is the framing that matters for a knowledge server. [P]

| Primitive | Control | Official framing |
|---|---|---|
| **Tools** | **model-controlled** | The model discovers and invokes them autonomously from context. https://modelcontextprotocol.io/specification/2025-06-18/server/tools |
| **Resources** | **application-controlled** | URI-addressed data sources, "like GET endpoints", providing data without significant computation or side effects; the host app decides what to attach. |
| **Prompts** | **user-controlled** | Exposed so the *user* can explicitly select them — about who decides *when*, not who authors the content. https://modelcontextprotocol.io/specification/2026-07-28/server/prompts |

(Note: `modelcontextprotocol.info` is an unofficial mirror — do not cite it as spec.)

**What a good knowledge MCP server exposes.** Anthropic's *Writing effective tools for AI
agents* [P] https://www.anthropic.com/engineering/writing-tools-for-agents:
namespace and name parameters unambiguously (`user_id`, not `user`); treat **tool
descriptions as prompts** and make implicit context (query formats, niche terms, how
resources relate) explicit; implement **pagination, range selection, filtering and/or
truncation with sensible defaults** for any response that could eat context, and steer the
agent with instructions when truncating; **explicitly encourage many small targeted
searches over one broad search** for knowledge retrieval; return human-readable fields
over raw IDs; and prompt-engineer *error* responses to be actionable rather than
tracebacks. The relayed claim that description refinements alone produced a
SWE-bench-Verified SOTA is **[U]** — not confirmed from the primary page.

**Known failure modes, with numbers.**

- **Tool-count bloat is measured.** **RAG-MCP** (arXiv 2505.03275) reports tool-selection
  accuracy of **43.13% with retrieval-filtered tools vs 13.62% with all tools in the
  prompt** (>3×), and **>50% prompt-token reduction**. [P]
  https://arxiv.org/abs/2505.03275 — **note the direction**: 13.62% is the *all-tools*
  baseline; several blogs report this reversed.
- **Anthropic:** tool results and definitions "can sometimes consume **50,000+ tokens**
  before an agent reads a request." [P]
  https://www.anthropic.com/engineering/code-execution-with-mcp
- Secondary, use with caution [S]: GitHub's official MCP server ≈**42,000 tokens** of tool
  definitions alone; ~**95% → ~71%** selection accuracy (24-pt drop) for a focused toolset
  vs the full server; ~**10%** degradation going 10 → 100 tools across GPT-4o-mini /
  Claude 3.5 Haiku / Gemini 2.0 Flash.
- **Mitigations**: progressive/on-demand tool loading; retrieval-based tool selection
  (RAG-MCP); pagination and truncation; returning **IDs + summaries instead of full
  documents**. Anthropic's *code execution with MCP* pattern — present servers as a code
  API tree the agent explores, loading only the definitions it needs and filtering data
  before it reaches context — is relayed as **~150,000 → ~2,000 tokens (98.7% reduction)**
  on an example workflow; the mechanism and the 50,000-token problem are [P] on that page,
  the **98.7% figure is [S]** (relays only).
- **Resources vs tools for a knowledge base.** The spec framing supports the split: a
  stable URI-addressable document the *host* chooses to attach is a **resource**; anything
  needing ranking, filtering or query interpretation is a **tool**. But **real-world
  client support for resources is [U]** — no official per-client feature matrix was found.
  **Assume tools are universally supported and resources are not**, and do not make
  resources load-bearing. (`spipe_knowledge_compiler.md` §7.1–7.3 already designed the URI
  space and the resources/tools split; this is the external evidence for keeping tools as
  the primary path.)
- **Security, even for a read-only local server.** **Tool poisoning** — malicious
  instructions embedded in *tool descriptions*, visible to the model but not the user —
  is demonstrated prior art, including a malicious server **overriding instructions from
  other trusted servers**. [P] https://invariantlabs.ai/blog/mcp-security-notification-tool-poisoning-attacks
  · codified as OWASP **MCP03:2025 Tool Poisoning**
  https://owasp.org/www-project-mcp-top-10/2025/MCP03-2025%E2%80%93Tool-Poisoning.
  For SPipe the live risk runs the other way: **indexed content is untrusted input**. Any
  README, code comment or captured page the index returns can carry injected directives.
  Returned content must be framed as data, and **indexed text must never influence tool
  selection**.

**Pure Simple, no network?** **Yes — and it already is.** `src/app/spipe_mcp/main.spl` is
543 lines of pure Simple speaking JSON-RPC over stdio.

**SPipe would build — three concrete repairs, not a new server:**

1. **Shrink the tool surface.** 33 tools on one server is squarely in the measured
   degradation band (RAG-MCP's baseline collapse, and the [S] 24-pt focused-vs-full drop).
   Collapse the `spipe_context_*` / `spipe_context_sql_*` / `spipe_codebase_*` families
   into a handful of tools taking a backend parameter. **Verified in-tree:** the SQL and
   non-SQL families really are parallel dispatch arms for the same operations —
   `_dispatch_tool` handles `spipe_context_get` / `spipe_context_get_tree` and
   `spipe_context_sql_get` / `spipe_context_sql_get_tree` as separate branches, and the
   `_search` variants likewise. Target **under ~10 tools**.
2. **Declare and implement `resources`.** `_spipe_initialize_payload` currently advertises
   `capabilities = {"tools": []}` only. A URI-addressed read-only resource per canonical
   document uid is exactly what `model/uid.spl` already produces, and it is the
   application-controlled path the spec intends for stable documents. Keep tools as the
   supported path (see the [U] above) and treat resources as additive.
3. **Bound every response.** Add pagination and truncation defaults to the search and
   `_get` tools, and return `{uid, path, line_range, content_hash, snippet}` rather than
   full bodies — which is also the §6 citation contract. Rewrite tool descriptions as
   prompts per Anthropic's guidance, stating query syntax and how the axes relate.

---

## 10. Addendum — at what corpus size does BM25-alone stop being enough?

**Direct answer: no published corpus-size threshold exists, and the question's premise is
slightly wrong.** BM25's failure mode is **vocabulary mismatch**, which is driven by *query
style* and *term distribution*, not by document count.

- BEIR's 18 datasets span roughly **3.6k to 5.4M documents** and BM25 remains a strong,
  frequently-winning zero-shot baseline **across that whole range** [P,
  https://arxiv.org/abs/2104.08663]. There is no reported inflection point. **Inference,
  not a cited result:** at 10^4–10^5 files, query phrasing dominates corpus size.
- The one quantified mismatch figure located is at **10^7 scale**: 988 of 6,980 MS MARCO
  dev queries (14.2%) where BM25 misses the gold passage in the top-1000 of 8.84M
  passages [S]. That is two to three orders of magnitude above SPipe's corpus and should
  **not** be extrapolated downward.
- What *does* change with corpus size is **polysemy density and near-duplicate pressure**
  — more documents share a term, so IDF discriminates less. **[U]** — no primary source
  quantifying this against a threshold was found.

**Cheapest local semantic signal that closes part of the gap, ordered by cost:**

1. **Pseudo-relevance feedback (RM3 / Rocchio).** Retrieve top-k, harvest expansion terms
   from those documents, re-query. Zero training, corpus statistics only, fully
   deterministic. Anserini's published BM25+RM3 run on TREC DL 2019 records **MAP .4270 /
   nDCG@10 .5180** [S] — **but no BM25 baseline was retrieved alongside it, so the lift is
   [U] this session.** The *technique's* standing as the default strong lexical baseline
   is [P] (it is the reference PRF baseline throughout the Anserini reproducibility
   literature).
2. **PMI / co-occurrence-based expansion.** Corpus-derived term association; GloVe is
   literally a factorisation of the same co-occurrence matrix, so the association signal
   is available without any factorisation at all. [P for the GloVe-co-occurrence
   relationship; retrieval lift [U]]
3. **Locally-trained word vectors** — Diaz/Mitra/Craswell's *local beats global* result
   [P, https://aclanthology.org/P16-1035.pdf], with the caveat that "local" there means
   per-query top-k, not once over the repo.
4. **Do NOT build LSA.** Atreya & Elkan is the primary counter-evidence: no LSI variant
   achieved a worthwhile improvement over BM25 on TREC. [P]

**And the non-obvious cheapest signal of all, for SPipe specifically:** the **link graph**
(§4). A document that a top-ranked hit *links to* is semantically related by human
authorship — a stronger and cheaper association signal than any locally-computed vector,
and SPipe already computes it in `graph/reverse_index.spl` and `fusion/graph_source.spl`.

---

## 11. Roadmap (evidence-ordered, cheapest-first)

| # | Work | Module | Evidence | Cost |
|---|---|---|---|---|
| 1 | ~50-query graded eval harness + gate | new `scripts/check/` + SDN gold set | §8 Buckley–Voorhees [P] | M (labels) |
| 2 | Graph source seeding + decay policy | `fusion/graph_source.spl` (exists) | §4 HippoRAG [P] | S |
| 3 | Proximity reranker over fused top-N | new `search/rerank_sdm.spl` | §3 PPM 5–11% MAP [P] | M |
| 4 | Structure-aware chunking | new `scan/chunks.spl` | §1 cAST [P] | M |
| 5 | Budget packing + citation emission | new `search/pack.spl` | §6 MMR [P], ALCE [P] | M |
| 6 | Card-tier progressive disclosure | `model/canonical.spl` + new card emitter | §5 Agent Skills [P] | M |
| 7 | MCP surface repair (see §9) | `src/app/spipe_mcp/main.spl` (exists) | §9 | M |
| 8 | Incremental/watch reindex (see §7) | new | §7 | L |
| — | **Do not build:** semantic chunking, LSA, LLM entity extraction, a "semantic" hashed embedding | — | §1 [P], §2 [P], §4 [P] | — |

Item 1 (the eval harness) should land **before** items 2–6, or none of their claimed
lifts are measurable in this repo. This ordering matches the TL;DR's build order.

## 12. References

All URLs are inline at point of use, with [P]/[S]/[U] labels. Sources gathered via
WebSearch snippets on 2026-09-05; see §0 for the tooling caveat.
