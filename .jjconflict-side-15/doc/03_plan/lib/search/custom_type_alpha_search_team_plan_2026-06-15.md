# Plan — Custom-Type Alpha Search Team

Created 2026-06-15. Companion research:
[`doc/01_research/lib/search/search_pattern_match_catalog_2026-06-15.md`](../../../01_research/lib/search/search_pattern_match_catalog_2026-06-15.md).
Sibling of the crypto (template) and compression plans.

## Prime directive
Same as the wave: **#1 deliverable is improving the Simple language** via the
bug/feature stream. Search is the **generics stressor** (`PostingList<Id>`,
`AnnNode<V>`, `Embedding<D>`). Custom types must carry behavior; primitive
workarounds get filed, never normalized.

## Dependency — shared foundation (BARRIER)
**Prerequisite:** crypto plan §Phase-0 shared custom-type foundation
(`src/lib/common/bytes/`: `ByteSpan`, `ByteBuffer`, `BitReader/Writer`, endian
ints, `RingWindow`, checksums). **Do not redefine these types.** Search work
fans out only after that barrier lands. `RingWindow` is shared with LZ
compression — single owner is the foundation module.

## Mode: alpha
Reuse `dual_backend.spl`. Here alpha compares **SIMD vs forced-scalar** custom-
type paths *and* (where a permissive C lib exists) **C oracle vs pure-Simple**.
Fail-closed on mismatch. Most items are already implemented on primitives — this
refactors them onto custom types and proves parity.

## C-implementation policy
Permissive (RE2, Hyperscan, StringZilla, Faiss, CRoaring, PCRE2, hnswlib) ⇒
vendor/bind under `src/runtime/vendor/**` as alpha oracle. Copyleft (GNU grep
dfa, Xapian, Sphinx) ⇒ write own minimal C oracle. Gate table in research doc.

## Phases

### Phase 0 — Foundation barrier
Consume crypto §Phase-0. Add only search-domain types from the research
"Custom-type layer" table (`Haystack`, `Pattern`, `MatchSpan`, `PostingList<Id>`,
`Embedding<D>`, `Score`) in `src/lib/common/search/types.spl`. Generics decision
mirrors the crypto seam probe: attempt `PostingList<Id>` as a true generic first;
file a language item if it forces erasure/`[u8]` fallback.

### Phase 1 — Exact + prefilter (disjoint scope)
| Sub-team | Scope | Custom types |
|----------|-------|--------------|
| S1 exact | memmem/Two-Way/Boyer-Moore in `common/search/exact.spl` | `Haystack`,`Pattern`,`MatchSpan` |
| S2 multi | Aho-Corasick over existing `trie/` | `TrieNode`, pattern set |
| S3 prefilter+regex | trigram/literal prefilter feeding existing `regex_engine/` | `Pattern`, candidate set |
| S4 SIMD seam | AVX2/NEON memchr/first-last-byte under scalar oracle | `ByteSpan` scan |

Staged subset: exact single+multi, glob, literal/trigram prefilter, SIMD memchr.
Enforce the core rule: **prefilter → candidate → regex/fuzzy verify → rank**.

### Phase 2 — Index + rank + ANN (deferred-heavy)
Inverted index + positional postings (`PostingList<Id>` merge), BM25 `Score`
ranking, roaring bitmap filters (CRoaring oracle), one ANN index (HNSW via
hnswlib oracle, `Embedding<D>`/`AnnNode<V>`). GPU vector search deferred to a
follow-up. DB index families (B+tree/LSM/GIN) stay with the database plan, not
duplicated here.

## Multi-agent structure
Orchestrator (Opus) owns barrier + merges + language-item triage + commits.
4 Sonnet sub-agents, **disjoint files**, parallel in one message after the
barrier, each told it has `advisor()`. Commit per lint-clean sub-batch.

## Language-improvement capture (first-class)
Expected hot spots (pre-seed): generics `<>` on `PostingList<Id>`/`AnnNode<V>`,
`array.get(n≥1)` corruption (directly on the hot scan path), iterator/`for-in`
vs index discrepancies, `me`-self-mutation on cursor advance, operator overload
for `Score` ordering, f64 unreliability for `Embedding` distance (use i64/text
verification per memory until fixed). File each via `bin/simple bug-add` /
`doc/02_requirements/feature/`. No items produced = red flag.

## Gates
`bin/simple test`, `bin/simple build lint`, search + foundation specs green,
alpha SIMD-vs-scalar and C-oracle parity green, `verify` → `STATUS: PASS`.
