# Research: State-of-the-Art Optimization Techniques for Code Clone Detection

**Date:** 2026-03-14
**Context:** Optimization opportunities for Simple's duplication checker (`src/compiler/90.tools/duplicate_check/`)
**Current stack:** Karp-Rabin rolling hash + cosine similarity + Ollama embeddings

---

## 1. Karp-Rabin Rolling Hash Optimizations

### 1.1 SIMD Vectorization (2-5x speedup)

**Technique:** Vectorize the rolling hash computation using SIMD instructions (SSE4/AVX2/NEON).

- Daniel Lemire's 2024 benchmarks show rolling Karp-Rabin achieves ~1 GB/s/core baseline
- SIMD implementation processes 4 hash windows in parallel per instruction
- Initial budget: 8-9 SIMD instructions per 4 bytes, with 4 being multiply/accumulate
- A blog post by Matt Sills (2024) reports >2.5x speedup with SIMD Rabin-Karp
- Chain dependency on multiplication (vpmulld latency=10 cycles, throughput=0.66 cycles) limits speedup

**Trade-offs:** Platform-specific code paths needed. Complex to implement. Only worthwhile when hashing is the bottleneck (currently tokenization likely dominates).

**Applicability:** Medium. Simple's `detector.spl` uses `h = (h * 31 + token_id) % 10^9+7`. SIMD would help if processing millions of tokens, but the tool operates on token IDs (integers), not raw bytes, so the vectorization pattern differs from string hashing.

### 1.2 Suffix Array Construction (10-150x for grouping)

**Technique:** Replace hash-table grouping with suffix array + LCP (Longest Common Prefix) array.

- SAGA (SANER 2020) builds suffix arrays over tokenized source code
- LCP array entries directly encode shared prefix lengths between adjacent suffixes
- Adjacent entries with LCP >= min_tokens are clone pairs — no hash table needed
- GPU-accelerated suffix array construction: 2.8s for 1.2M tokens (vs 439s CPU = 150x)
- CPU suffix array construction via SA-IS algorithm: O(N) time, O(N) space
- On 100MLOC: suffix array built in 1m2s (9% of total), finding Type-1/2 clones in 5m0s (46%)

**Trade-offs:** Higher implementation complexity. Suffix arrays find ALL repeated substrings at once (not just fixed-window), which is more powerful but produces more results to filter. Memory: suffix array + LCP = 2N integers.

**Applicability:** High. This would replace the current sliding-window + hash-table approach entirely. Instead of hashing each window and grouping by hash, build a suffix array over the entire token sequence and read off all duplicated subsequences from the LCP array. Eliminates hash collisions entirely.

### 1.3 Winnowing / Document Fingerprinting (reduce fingerprint count by ~60%)

**Technique:** Instead of storing a hash for every window position, select only the minimum hash in each window of size w.

- Schleimer, Wilkerson & Aiken (SIGMOD 2003) — used by MOSS plagiarism detector
- Guarantees: any match of length >= t (threshold) will be detected
- Reduces stored fingerprints to within 33% of theoretical minimum
- Selection rule: pick minimum hash in window; if tie, pick rightmost
- Parameter tuning: k (k-gram size) should be minimum that eliminates coincidental matches

**Trade-offs:** Slightly reduces detection sensitivity for short clones near the threshold. Adds a second windowing pass. But dramatically reduces index size and comparison count.

**Applicability:** High. Can be layered on top of current Karp-Rabin hashing. Instead of storing all N window hashes, store only ~0.4N selected fingerprints. Reduces both memory and grouping time proportionally.

### 1.4 Cyclic Polynomial Hash / BuzHash (avoid multiplication)

**Technique:** Replace polynomial hash with cyclic polynomial (bit rotation + XOR).

- Avoids multiplication entirely — uses barrel shift + XOR
- Trivially invertible: O(1) to add and remove characters from window
- Used in rsync, content-defined chunking
- Comparable collision rates to polynomial hashing for practical window sizes

**Trade-offs:** Slightly worse theoretical hash distribution than polynomial. But multiplication-free means better pipeline throughput on simple cores.

**Applicability:** Medium. Simple alternative to current `h * 31 + id` formula. Would simplify the rolling update (currently needs to track `base^window_size` for removal).

---

## 2. Semantic Clone Detection Tool Optimizations

### 2.1 SourcererCC: Inverted Index + Sub-block Filtering (scales to 250MLOC)

**Technique:** Partial inverted index with filtering heuristics.

**Key innovations:**
1. **Sub-block Overlap Filtering:** Only index the least-common tokens per block (not all tokens). Two blocks can only be clones if their sub-blocks share at least one term
2. **Token Position Filtering:** Exploit token ordering within blocks to compute live upper/lower bounds on similarity. Prune candidates whose upper-bound < threshold, accept candidates whose lower-bound > threshold — without computing full similarity
3. **Partial Index:** Index only a subset of tokens (those with lowest document frequency), reducing index size by 80-90%

**Performance:** 250MLOC on a standard workstation. Only tool to achieve Type-3 detection at 100MLOC scale (NiCad fails at 100MLOC, CCFinderX only handles Type-1/2).

**Applicability:** Very High. The cosine similarity phase (`features.spl`) currently does O(B^2) pairwise comparisons capped at 500 blocks. SourcererCC's filtering could reduce this dramatically. Specifically:
- Build an inverted index mapping each token to blocks containing it
- For each query block, only compare against blocks sharing rare tokens
- Use upper/lower bound pruning to skip full cosine computation

### 2.2 CloneWorks: Input Partitioning + Sub-block Filtering (250MLOC in 4 hours)

**Technique:** Memory-bounded processing via input partitioning.

**Key innovations:**
1. **Input Partitioning:** Split code fragments into partitions that fit in memory; detect within each partition independently
2. **Sub-block Filtering:** Same as SourcererCC — index least-common terms only
3. **Modified Jaccard Similarity:** Alternative to cosine that works well with token sets

**Performance:** 250MLOC in ~4 hours on a quad-core workstation with 10GB RAM.

**Applicability:** High. The partitioning strategy is directly applicable when Simple's codebase grows beyond memory capacity. Current `max_blocks_to_analyze=500` cap is a crude version of this — proper partitioning would handle more blocks without the hard cap.

### 2.3 CCAligner: Token-based with Gap Handling (Type-3 specialized)

**Technique:** Modified Longest Common Subsequence that tolerates gaps (inserted/deleted lines).

- Handles "big gap clones" — clones with large blocks of inserted/modified code
- Uses e-mismatches in windowed token comparison
- Fills a gap in detection that SourcererCC and NiCad miss

**Applicability:** Medium. Could complement current exact-match detection for cases where functions have been partially modified.

### 2.4 SAGA: GPU-Accelerated Suffix Arrays (50-70x faster than SourcererCC)

**Technique:** Suffix array construction + LCP computation on GPU with data chunking.

**Key innovations:**
1. **Data Chunking:** Divide token sequence into chunks that fit in GPU memory; construct suffix arrays per chunk pair
2. **GPU Suffix Array:** 150x faster than CPU for 1.2M tokens
3. **Type-3 via Iterative Merging:** Merge adjacent "mergeable" suffix array neighbors until gap threshold exceeded

**Performance breakdown on 100MLOC:**
- Preprocessing/tokenization: 3m48s (35%)
- Suffix array construction: 1m2s (9%)
- Type-1/2 clone finding: 5m0s (46%)
- Type-3 + post-processing: 1m7s (10%)
- **Total: 10m57s** (vs SourcererCC ~8-9 hours, CCFinder ~12 hours)

**Applicability:** Medium-Low for now. Requires CUDA. But the suffix array approach (without GPU) is highly applicable — see section 1.2.

### 2.5 TACC: Token-filter + AST-verify Hybrid (100MLOC in 3h48m)

**Technique:** Two-phase: cheap token-based filtering, then expensive AST-based verification.

- Phase 1: Low-threshold token similarity to generate candidates (fast, high recall)
- Phase 2: AST comparison to verify candidates (accurate, lower recall but removes false positives)

**Applicability:** Medium. Could apply to Simple's pipeline: use Karp-Rabin hash for candidate generation, then cosine similarity only on candidates (instead of all-pairs).

---

## 3. Embedding-Based Clone Detection

### 3.1 SSCD: LLM Ensemble + kANN Search

**Technique:** Generate code embeddings with LLMs, find clones via k-approximate nearest neighbor search.

**Key innovations:**
1. **Multi-model Ensemble:** Use 2+ LLM embedding models (e.g., CodeT5+110M, CuBERT, SPTCode) and aggregate results
2. **kANN Search:** Avoid O(N^2) pairwise comparison — use approximate nearest neighbor to find similar embeddings in O(N log N)
3. **GPU-accelerated search:** Parallel similarity search on GPU

**Top-performing models for clone detection (2025 evaluation):**
- CodeT5+110M
- CuBERT
- SPTCode

**Applicability:** High. Simple currently uses Ollama (`nomic-embed-text`, 768-dim). The kANN approach would replace the current O(D^2 * 768) pairwise cosine with O(D log D) approximate search.

### 3.2 FAISS IVF-PQ: Practical ANN at Scale

**Technique:** Inverted File Index + Product Quantization for billion-scale vector search.

**How it works:**
1. **IVF:** Cluster embeddings into `nlist` clusters via K-Means. At query time, only search `nprobe` nearest clusters
2. **PQ:** Split 768-dim vector into M sub-vectors (e.g., M=96, each 8-dim). Quantize each to 256 centroids (8 bits). Compress 768 floats (3072 bytes) to 96 bytes = 32x compression
3. **Precomputed tables:** Accelerate distance computation using lookup tables

**Performance characteristics:**
- 1B vectors: index fits in ~54 GiB (vs 360 GiB raw) with 4-5x compression
- Query time: milliseconds for top-k results
- Recall: 85-95% depending on nprobe setting
- Training: need ~256K vectors minimum for good centroids

**Recommended setup for code clone detection:**
```
nlist = sqrt(N)           # number of IVF clusters
nprobe = nlist / 10       # clusters to search per query
M = 96                    # PQ sub-vectors (for 768-dim)
nbits = 8                 # bits per sub-quantizer
```

**Applicability:** High, but only when embedding count exceeds ~10K. For Simple's current scale (~2,600 files), brute-force cosine is fine. FAISS becomes essential at 50K+ embeddings. Can be integrated via SFFI to FAISS C API.

### 3.3 Locality-Sensitive Hashing (LSH)

**Technique:** Hash similar vectors to same bucket with high probability.

**Variants:**
- **Random Projection LSH:** Project vectors onto random hyperplanes; bits = which side each projection lands on. Simple, fast, but needs many hash tables for good recall
- **DET-LSH (2024):** Dynamic Encoding Tree structure — 6x faster index construction, 2x faster queries vs prior LSH
- **Multi-Index LSH:** Achieves up to 85% recall with 67% memory reduction via learned hash functions + quantization
- **McCauley (2024):** Function inversion to compress LSH structures without performance penalty

**Trade-offs vs FAISS:**
- LSH: simpler, no training needed, streaming-friendly, but lower recall per bit
- FAISS IVF-PQ: higher recall, better compression, but needs training phase

**Applicability:** Medium-High. LSH is attractive because it requires no training (unlike IVF-PQ) and supports incremental insertion. For Simple's embedding cache, LSH could provide instant similarity search without an offline index-building step.

### 3.4 Embedding Dimensionality Reduction

**Technique:** Reduce 768-dim embeddings before comparison.

- **PCA to 128-256 dims:** Often retains 95%+ variance. 3-6x speedup in distance computation
- **Random projection:** Even simpler, provably preserves distances (Johnson-Lindenstrauss lemma)
- **Matryoshka embeddings:** Some models (e.g., nomic-embed) support truncating to smaller dimensions natively

**Applicability:** High. Reducing `nomic-embed-text` 768-dim to 256-dim would give 3x speedup on cosine similarity with minimal accuracy loss. Check if `nomic-embed-text` supports Matryoshka — if so, just truncate vectors.

---

## 4. Incremental Clone Detection

### 4.1 Index-based Incremental Detection

**Technique:** Persist the clone detection index; on code changes, update only affected entries.

**Approaches:**
1. **Token cache invalidation (already implemented):** Simple's `cache.spl` checks file mtime and re-tokenizes only changed files. This is the foundation
2. **Incremental index update:** When a file changes, remove its old entries from the inverted index and insert new ones. No need to re-index unchanged files
3. **Clone class representatives:** Only compare new/changed code against one representative per existing clone class (not all members)

**Paper:** Goesele et al. (ICSM 2009) — "Incremental Clone Detection"
- Store clone detection results in database
- On change: re-analyze only changed files + their clone partners
- Speedup: proportional to change size (small change = near-instant)

**Applicability:** Very High. Simple's `incremental.spl` already caches file-level results in `.duplicate_cache.sdn`. To go further:
- Persist the hash → location index between runs
- On file change: remove old hashes, insert new ones, re-check only affected groups
- Expected speedup: 10-100x for incremental runs on large codebases

### 4.2 Siamese: Multi-Representation Incremental Search

**Technique:** Elasticsearch-backed code clone search with incremental index updates.

**Key innovations:**
1. **Multiple code representations:** Transform code into original tokens, normalized tokens (Type-2), and blind-renamed tokens (Type-3) simultaneously
2. **Query reduction:** Select search keywords based on uniqueness (IDF-like). Common tokens (if, return, =) are dropped from queries
3. **Elasticsearch index:** Supports incremental document add/remove without rebuilding
4. **Custom ranking function:** Score candidates by clone type preference

**Performance:** 365MLOC searchable in <8 seconds per query. 95-99% mean average precision.

**Applicability:** Medium. The multi-representation idea is excellent — generate multiple normalizations per block and index all of them. But Elasticsearch is heavy infrastructure. The query reduction technique (drop common tokens from index) is directly applicable to Simple's inverted index approach.

### 4.3 Content-Addressed Caching

**Technique:** Hash file content (not path) to enable cache hits across renames/moves.

- Current `cache.spl` uses filepath → (mtime, tokens). If a file is renamed, cache misses
- Content-addressed: hash(file_content) → tokens. Rename = cache hit
- Git blob hashes can serve as content addresses for tracked files

**Applicability:** High. Simple change to existing cache. Use content hash as primary key, filepath as secondary lookup.

---

## 5. Parallel Clone Detection

### 5.1 File-Level Parallelism (linear speedup)

**Technique:** Process files independently in parallel for tokenization and hashing.

- Tokenization is embarrassingly parallel — each file independent
- Feature extraction (cosine) per file is independent
- Only the grouping/comparison phase needs synchronization

**Expected speedup:** Near-linear with core count for tokenization phase. 4 cores = ~3.5x.

**Applicability:** Very High. Simple's `parallel.spl` is currently stubbed. Implement with Simple's async/actor system:
- Actor per file for tokenization
- Merge hash tables via concurrent hash map or actor message passing
- Comparison phase: partition block pairs across actors

### 5.2 MapReduce Pattern (distributed)

**Technique:** Map = tokenize + hash per file. Reduce = group by hash + verify.

- Nasehi et al. (2012): MapReduce for clone detection on Hadoop
- SNCD (2025): Distributed clone detection with MapReduce + HDFS + partial indexing + multi-threading
- Map phase: each mapper tokenizes assigned files, emits (hash, location) pairs
- Reduce phase: each reducer collects all locations for a hash, verifies clones

**Applicability:** Low for current scale. Useful if Simple needs cross-repository clone detection across hundreds of projects.

### 5.3 GPU Acceleration

**Technique:** Offload specific computations to GPU.

**Best candidates for GPU offload:**
1. **Suffix array construction:** 150x speedup (SAGA)
2. **Cosine similarity matrix:** Batch matrix multiplication on GPU. For N vectors of dim D: GPU computes N*N similarity matrix in one cublasSgemm call
3. **Embedding generation:** Already GPU-accelerated if Ollama uses GPU
4. **LSH bucket computation:** Batch random projections = matrix multiply

**Applicability:** Medium. Simple has CUDA backend support. Could be relevant when processing 10K+ blocks. For current scale (<3K files), CPU parallel is sufficient.

### 5.4 Work-Stealing for Load Balancing

**Technique:** Dynamic task distribution where idle threads steal work from busy threads' queues.

- Files vary greatly in size — static partitioning leads to load imbalance
- Work-stealing: each thread has a deque of file tasks; idle threads steal from the tail of busy threads' deques
- Lock-free Chase-Lev deque for low overhead

**Applicability:** Medium. Only matters when file sizes are highly skewed. Simple's codebase has files ranging from 10 to 2000+ lines, so some imbalance exists but may not justify the complexity.

---

## 6. Token-Based vs AST-Based vs PDG-Based: Scaling Comparison

### 6.1 Scaling Characteristics

| Approach | Preprocessing | Comparison | Max Proven Scale | Clone Types |
|----------|--------------|------------|-----------------|-------------|
| **Token (hash)** | O(N) | O(N) to O(N log N) | 250MLOC (CloneWorks) | Type-1, 2, partial 3 |
| **Token (suffix)** | O(N) | O(N) | 100MLOC (SAGA, 11min) | Type-1, 2, 3 |
| **AST (tree)** | O(N) parse | O(N^2) naive, O(N log N) hashed | 100MLOC (TACC, 3h48m) | Type-1, 2, 3 |
| **PDG (graph)** | O(N^2) build CFG/PDG | O(N^3) subgraph iso | ~60K files max | Type-1, 2, 3, 4 |
| **Hybrid token+AST** | O(N) tokenize + selective parse | O(N log N) filter + O(K) verify | 100MLOC (TACC) | Type-1, 2, 3 |
| **Embedding (LLM)** | O(N*D) embed | O(N log N) ANN | millions of functions | Type-1, 2, 3, 4 |

### 6.2 Hybrid Approach Recommendations for Simple

**Current:** Token (Karp-Rabin) + Token frequency (cosine) + Embedding (Ollama)

**Recommended hybrid pipeline:**

```
Phase 1: Token Karp-Rabin hash (current)     → exact clones    [O(N), fast]
Phase 2: Token inverted index + filtering     → near-miss       [O(N log N), SourcererCC-style]
Phase 3: Embedding + ANN search              → semantic clones  [O(N log N), when Ollama available]
```

- Drop the O(B^2) all-pairs cosine in favor of inverted-index filtered comparison
- This gives the same 3-tier detection (exact, near-miss, semantic) but scales to 100MLOC+

### 6.3 CCStokener: Semantic Tokens (Hybrid Token + AST)

**Technique:** Augment tokens with AST path information to create "semantic tokens."

- Extract AST paths between tokens for structural context
- Embed token + AST path as a single representation
- Captures structure without full AST comparison cost
- Better at Type-3 clone detection than pure token methods

**Applicability:** Medium. Would require AST information from Simple's parser. Could be a future enhancement.

---

## 7. Memory Optimization

### 7.1 Bloom Filters for Duplicate Hash Pre-screening

**Technique:** Before inserting a hash into the main index, check a Bloom filter. If absent, skip (no possible duplicates).

- Bloom filter: O(1) insert, O(1) query, configurable false positive rate
- At 1% FP rate: ~10 bits per entry
- At 0.1% FP rate: ~14 bits per entry
- Purpose: quickly identify which hashes appear more than once (potential clones). Non-duplicated hashes (majority) never need full index storage

**Expected savings:** In a typical codebase, 80-95% of hash windows are unique. Bloom filter identifies these with ~10 bits each vs storing full hash + location (64+ bits). Memory savings: 5-6x for the non-duplicate majority.

**Applicability:** High. Insert each window hash into a counting Bloom filter. On second occurrence, promote to the full hash table. This keeps the main index small (only potential duplicates).

### 7.2 Xor Filters (superior to Bloom for static sets)

**Technique:** Perfect hash-based filter with better performance than Bloom filters.

- **Memory:** 1.23 * log2(1/epsilon) bits per key — more efficient than Bloom's 1.44 * log2(1/epsilon)
- **Query:** Exactly 3 memory accesses (constant, unlike Bloom's k hash functions)
- **Speed:** 25.9% faster queries, 16% less space than Bloom filters
- **Binary Fuse Filters (2022):** Even faster construction, <20% space overhead

**Trade-offs:** Immutable once built — cannot add entries. Must rebuild for changes. Good for batch processing, bad for streaming.

**Applicability:** Medium. Best for the batch duplicate check mode (run_check.spl). For incremental mode, stick with Bloom filters (support insertion).

### 7.3 Fingerprint Compression

**Technique:** Store compressed fingerprints instead of full hashes.

- **Truncated hashes:** Store only bottom 32 bits of 64-bit hash. Doubles collision rate but halves memory
- **Variable-length encoding:** Most hash differences are small when sorted — use delta encoding + varint
- **Sorted + delta encoded:** Sort hashes, store deltas. Typical compression: 3-5x

**Implementation for Simple's hash index:**
```
1. Collect all window hashes
2. Sort them
3. Compute deltas between consecutive hashes
4. Varint-encode deltas (most deltas fit in 1-2 bytes vs 8 bytes for full hash)
5. Binary search on prefix sums for lookup
```

**Applicability:** High for `run_check.spl` which already sorts hashes. Delta encoding the sorted array would reduce memory ~4x.

### 7.4 Streaming / Online Processing

**Technique:** Process files in a stream without loading all data into memory.

- Current `run_check.spl` reads ALL files into memory, then processes
- Streaming alternative: read one file at a time, compute hashes, write to disk-backed index
- Memory usage: O(1) per file instead of O(total_lines)
- Use memory-mapped file for the hash index

**Applicability:** Medium-High. Important when the codebase exceeds available RAM. Current codebase (623K lines) fits comfortably in memory, but good practice for scalability.

### 7.5 Token Interning Optimization

**Technique:** Current `TokenInterner` maps strings to integer IDs. Optimize the string storage.

- **Arena allocation:** Allocate all interned strings in a contiguous arena. Reduces allocator overhead and improves cache locality
- **String deduplication statistics:** Track how many unique tokens exist. If <65K unique tokens (common), use 16-bit IDs instead of 64-bit
- **Perfect hashing:** For a known token vocabulary, use minimal perfect hash function (MPHF) for O(1) lookup with no collisions

**Applicability:** Medium. Current interning already deduplicates. 16-bit token IDs would halve the token stream memory if vocabulary is small enough.

---

## 8. Prioritized Implementation Roadmap

Based on impact, implementation effort, and applicability to Simple's current architecture:

### Tier 1: Quick Wins (1-2 days each, high impact)

| # | Optimization | Expected Speedup | Effort |
|---|-------------|-------------------|--------|
| 1 | **Winnowing filter** on Karp-Rabin hashes | 60% less memory, fewer comparisons | Low |
| 2 | **Inverted index** for cosine phase (replace all-pairs) | 10-100x for near-miss detection | Medium |
| 3 | **Content-addressed cache** (hash content, not path) | Better cache hit rate | Low |
| 4 | **Bloom filter pre-screening** for hash index | 5x memory reduction | Low |
| 5 | **Query reduction** (drop common tokens from index) | 2-3x fewer candidates | Low |

### Tier 2: Significant Improvements (3-5 days each)

| # | Optimization | Expected Speedup | Effort |
|---|-------------|-------------------|--------|
| 6 | **File-level parallelism** (tokenize + hash in parallel) | ~3.5x on 4 cores | Medium |
| 7 | **Suffix array** (replace hash grouping entirely) | Find all clones at once, no collisions | High |
| 8 | **Embedding dimensionality reduction** (768 -> 256 dim) | 3x cosine speedup | Low |
| 9 | **Delta-encoded sorted hashes** in run_check.spl | 4x memory reduction | Medium |
| 10 | **Incremental index persistence** (persist hash index between runs) | 10-100x for incremental | Medium |

### Tier 3: Advanced / Future (1-2 weeks each)

| # | Optimization | Expected Speedup | Effort |
|---|-------------|-------------------|--------|
| 11 | **FAISS IVF-PQ** for embedding search | O(N^2) -> O(N log N) semantic search | High |
| 12 | **LSH** for streaming embedding similarity | No training needed, incremental | High |
| 13 | **GPU suffix array** (via CUDA backend) | 150x suffix array construction | Very High |
| 14 | **Multi-representation indexing** (Siamese-style) | Better Type-2/3 recall | High |
| 15 | **SourcererCC-style partial index + position filtering** | Full SourcererCC scalability | High |

---

## 9. Key References

### Tools
- **SourcererCC** — Sajnani et al., ICSE 2016. Inverted index + sub-block filtering. 250MLOC. [Paper](https://dl.acm.org/doi/10.1145/2884781.2884877)
- **SAGA** — Li et al., SANER 2020. GPU suffix arrays. 100MLOC in 11min. [Paper](https://ieeexplore.ieee.org/document/9054832/) | [GitHub](https://github.com/FudanSELab/SAGA)
- **CloneWorks** — Svajlenko & Roy, ICSE 2017. Input partitioning + sub-block filter. 250MLOC in 4h. [Paper](https://dl.acm.org/doi/10.1109/ICSE-C.2017.3)
- **Siamese** — Ragkhitwetsagul & Krinke, EMSE 2019. Multi-representation + Elasticsearch. 365MLOC in 8s/query. [Paper](https://link.springer.com/article/10.1007/s10664-019-09697-7) | [GitHub](https://github.com/siamesetool/siamese)
- **CCStokener** — JSS 2023. Semantic tokens from AST paths. [Paper](https://www.sciencedirect.com/science/article/abs/pii/S0164121223000134)
- **TACC** — Wu et al., ICSE 2023. Token filter + AST verify hybrid. 100MLOC in 3h48m. [Paper](https://wu-yueming.github.io/Files/ICSE2023_TACC.pdf)
- **CCAligner** — Wang et al. Token-based with gap handling for Type-3.
- **SSCD** — Ahmed et al., SPE 2024. BERT-based + kANN. Industrial scale. [Paper](https://onlinelibrary.wiley.com/doi/full/10.1002/spe.3355)
- **SNCD** — 2025. Distributed MapReduce + partial index. [Paper](https://www.sciencedirect.com/science/article/abs/pii/S0167739X2500038X)

### Algorithms & Data Structures
- **Winnowing** — Schleimer, Wilkerson & Aiken, SIGMOD 2003. Document fingerprinting. [Paper](https://theory.stanford.edu/~aiken/publications/papers/sigmod03.pdf)
- **Xor Filters** — Graf & Lemire, 2019. Faster/smaller than Bloom. [Paper](https://arxiv.org/abs/1912.08258)
- **Binary Fuse Filters** — Graf & Lemire, JEA 2022. Even better than Xor. [Paper](https://dl.acm.org/doi/full/10.1145/3510449)
- **FAISS** — Douze et al., 2024. Vector similarity search library. [Paper](https://arxiv.org/abs/2401.08281) | [Docs](https://faiss.ai)
- **DET-LSH** — Wei et al., 2024. Dynamic Encoding Tree LSH. 6x faster index, 2x faster queries.
- **Daniel Lemire's rolling hash benchmarks** — 2024. SIMD Karp-Rabin analysis. [Blog](https://lemire.me/blog/2024/02/04/how-fast-is-rolling-karp-rabin-hashing/)
- **LLM Selection for SSCD** — Oct 2025. 76 LLMs evaluated for clone detection. [Paper](https://arxiv.org/abs/2510.15480)

### Incremental Detection
- **Goesele et al.** — ICSM 2009. Index-based incremental clone detection. [Paper](https://ieeexplore.ieee.org/document/5609665/)
- **Just-in-Time Clone Detection** — ICPC 2010. Compare only new code vs clone class representatives. [Paper](https://seal-queensu.github.io/publications/pdf/ICPC-Liliane-2010.pdf)
