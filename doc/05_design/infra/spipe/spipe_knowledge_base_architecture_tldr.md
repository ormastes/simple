# TL;DR — SPipe Knowledge Base Architecture

Full doc: [spipe_knowledge_base_architecture.md](spipe_knowledge_base_architecture.md)

**The problem is wiring, not algorithms.** The knowledge compiler (3,952 lines,
11 units) exposes 2 CLI verbs and has no gate; the MCP server next door (itself undeployed)
imports `app.spipe.*` zero times; the one persisted-capable index
(`InvertedIndex`) has zero product consumers while **two** per-query BM25 scanners run
beside it. Six disjoint SPipe locations, none aware of the others.

**Seven decisions.** (1) One `kb.spl` library, three thin transports — no new
server. (2) `InvertedIndex` becomes the persisted index; both scanners route
through it. (3) Structure-aware chunking, byte-addressed, corpus-tiered
(`doc/06_spec` is 16,824 files / 7.5M lines and must be tiered, not indexed
flat). (4) lexical → graph → RRF (`k=60`) → proximity rerank → budget pack.
(5) Eval harness lands **first**, with a sabotage arm proving it can go red.
(6) Citations are file + byte range (`Citation{ByteSpan, content_hash, …}`),
offline-verifiable by re-hashing; `SourceRange` stays frozen for link edges.
(7) Cards by default, bodies on demand; pair-select automated over the corpora
that already exist.

**Not built, on evidence:** semantic chunking, LSA, LLM entity extraction,
hashed pseudo-embeddings, Leiden, promotion, GitHub writeback. No `f64`
anywhere (native Dict gap) — per-mille `i64` and a log2 table.

<!-- sdn-diagram:id=spipe.kb.architecture -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spipe.kb.architecture hash=sha256:auto render=ascii
@layout dag
@direction LR

chunkers -> inverted_index
manifest -> inverted_index
inverted_index -> rrf_fuse
graph_source -> rrf_fuse
rrf_fuse -> rerank_sdm
rerank_sdm -> pack_cite
pack_cite -> kb_facade
kb_facade -> cli_verbs
kb_facade -> spipe_mcp
kb_facade -> ctx_tools
eval_gate -> rrf_fuse
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spipe.kb.architecture hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

Legend: `chunkers`, `manifest`, `pack_cite`, `rerank_sdm`, `eval_gate`,
`kb_facade` are NEW; `inverted_index`, `graph_source`, `rrf_fuse`, `spipe_mcp`,
`ctx_tools` EXTEND existing modules. Landing order is left-to-right with
`eval_gate` first — no stage may claim a lift it cannot measure.
