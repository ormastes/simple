<!-- codex-research -->

# Research — Search / Pattern-Match / Index / SIMD / GPU Catalog (custom-type-first)

Created 2026-06-15. Sibling of the crypto and compression catalogs in the same
wave. Companion plan:
[`doc/03_plan/lib/search/custom_type_alpha_search_team_plan_2026-06-15.md`](../../../03_plan/lib/search/custom_type_alpha_search_team_plan_2026-06-15.md).

Shared custom-type foundation is defined once in the **crypto plan §Phase-0**
(`src/lib/common/bytes/`); this doc only adds search-domain types. Adjacent
existing research: `doc/01_research/lib/strings/strings.md`,
`text_validity_presence_pattern_2026-02-24.md`,
`doc/01_research/lib/database/database_ecosystem_overview_2026-01-21.md`,
`doc/01_research/compiler/simd/`.

## Purpose & target

Same as the wave: **improve the Simple language** by rebuilding byte/text-heavy
search on intensive custom types instead of `[u8]`/`text`/`i64`. Search is the
best generics stressor of the three (posting lists, tries, automata, ANN graphs
are all parametric containers).

## In-tree status

| Area | In-tree | Path |
|------|---------|------|
| regex engine | yes | `src/lib/common/regex/`, `regex_engine/` |
| trie | yes | `src/lib/common/trie/` |
| suffix tree | yes | `src/lib/common/susffix_tree/` (note typo dir) |
| bloom filter | yes | `src/lib/common/bloom_filter/` |
| tree indexes | yes | `kd_tree/`, `b_tree/`, `red_black_tree/`, `avl_tree/`, `interval_tree/`, `segment_tree/`, `fenwick_tree/`, `quadtree/` |
| skip list | yes | `src/lib/common/skip_list/` |
| search app | yes | `src/app/search/` |
| DB accel | yes | `src/lib/nogc_sync_mut/db/accel.spl` |

**Conclusion:** broad coverage exists on primitives. New work = custom-type
refactor + alpha SIMD/scalar parity, not greenfield.

## Catalog (external map; plan picks the staged subset)

- **Exact single-pattern:** memchr/memmem, Two-Way (Crochemore-Perrin), KMP,
  Boyer-Moore(-Horspool), Sunday, Rabin-Karp, Z-algo, BNDM/Shift-Or, suffix
  array, FM-index/BWT.
- **Exact multi-pattern:** trie, double-array trie, Aho-Corasick (+PFAC for GPU),
  Commentz-Walter, Wu-Manber, DAFSA, Hyperscan-style hybrid.
- **Regex models:** backtracking VM (PCRE2), Thompson NFA, Pike VM (RE2), lazy/
  tagged DFA, Glushkov, Brzozowski/Antimirov derivatives, hybrid+literal prefilter.
- **Glob/wildcard:** recursive/DP/two-pointer glob, path-segment trie, gitignore
  pathspec, SQL LIKE (trigram), router radix tree.
- **Approximate/fuzzy:** Levenshtein/Damerau, Hamming, Jaro-Winkler, Myers
  bit-vector, Ukkonen, bitap, Levenshtein automata, BK-tree/VP-tree, q-gram,
  MinHash/SimHash/LSH, Soundex/Metaphone; alignment Needleman-Wunsch/Smith-
  Waterman/WFA.
- **Full-text:** inverted index + positional postings, skip blocks, block-max
  WAND/MaxScore, FST term dict, roaring bitmap, n-gram/permuterm; ranking
  Boolean/TF-IDF/BM25(F)/DFR/LM/LTR/RRF/PageRank.
- **DB indexes:** B+tree, hash/extendible/linear, bitmap/roaring, GIN/GiST/SP-GiST/
  BRIN/bloom, zone maps, LSM (memtable skiplist + SSTable), Bw-tree, ART/Patricia,
  HAMT, Masstree; spatial R-tree/R*-tree/kd/ball/cover/VP, geohash/S2/H3, BKD,
  Z-order/Hilbert; JSON/XML/graph (VF2/VF3, 2-hop labeling).
- **Vector/ANN:** flat/BLAS exact kNN + top-k; HNSW/NSG/Vamana/DiskANN/CAGRA,
  IVF-Flat/SQ/PQ, OPQ/RVQ, scalar/binary quant, LSH, Annoy, ScaNN, SPTAG.
- **SIMD:** vectorized memchr, first/last-byte filter, AVX2/AVX-512/NEON/SVE/SWAR
  compare masks, Teddy multi-literal, vectorized rolling hash, posting-list
  intersection/decompression (varint/BP128/FOR), SIMD distance/popcnt.
- **GPU:** brute-force/IVF/PQ vector kNN (good), PFAC/Wu-Manber packet/DNA scan,
  columnar string contains/regex, GPU suffix array/FM-index/Smith-Waterman; bad
  fits: single small regex, file-tree traversal, B-tree point lookup.
- **FS find:** DFS/BFS traversal + visited set, fnmatch/glob, pathspec trie,
  plocate-style name index, parallel grep work-stealing.

## Custom-type layer (search-domain, atop `src/lib/common/bytes/`)

| Primitive today | Custom type | Behavior |
|-----------------|-------------|----------|
| `[u8]`/`text` haystack | `Haystack` (over `ByteSpan`) | char/byte iteration, `find_from(cursor)` |
| `[u8]` needle | `Pattern` | precomputed skip tables, `len` invariant |
| `i64` position | `MatchPos` / `MatchSpan` | typed start/end, no bare-int confusion |
| `i64` doc id list | `PostingList<Id>` (generic) | sorted-merge `intersect`/`union`, skip cursor |
| node ptrs | `TrieNode`, `NfaState`, `AnnNode<V>` | parametric containers (generics stressor) |
| `f64[]` vector | `Embedding<D>` | typed dim, `dot`/`l2` ops, quantize |
| ranking score | `Score` | ordered, fused-accumulate, top-k heap key |

Generics emphasis: `PostingList<Id>` and `AnnNode<V>` are the deliberate `<>`
probes. Behavior-carrying required (advisor rule).

## C reuse license gate

| Library | License | Posture |
|---------|---------|---------|
| RE2 | BSD | **permissive** oracle (regex) |
| Hyperscan | BSD | **permissive** oracle (multi-regex/SIMD) |
| StringZilla | Apache/BSD | **permissive** oracle (SIMD/GPU string) |
| simdutf | MIT/Apache | **permissive** (UTF-8 validate) |
| CRoaring | Apache | **permissive** (bitmaps) |
| Faiss | MIT | **permissive** oracle (ANN/GPU) |
| hnswlib/nmslib/Annoy/FLANN/nanoflann | Apache/BSD | **permissive** (ANN/trees) |
| PCRE2 | BSD | **permissive** (Perl regex) |
| GNU grep dfa | GPL | **copyleft ⇒ write own C** oracle |
| Xapian / Sphinx | GPL | copyleft ⇒ avoid for oracle |

## Core engineering rule (carry into plan)
Do **not** run regex/fuzzy first when literals can prefilter:
`literal/trigram/prefix prefilter → candidate set → regex/fuzzy verify → rank`.
SIMD for in-memory byte scans; GPU only for large batched/on-device workloads.

## Verification implications
- Alpha: SIMD (AVX2/NEON) vs forced-scalar custom-type path, byte-for-byte.
- C oracle (RE2/Faiss) parity for match sets and top-k ordering.
- Property tests on `PostingList<Id>` merge and `Embedding<D>` distance.
