# Research: Duplication Detection Algorithms in Simple Compiler

**Date:** 2026-03-14
**Scope:** `src/compiler/90.tools/duplicate_check/` (17 files, ~3,110 lines)

---

## Architecture Overview

The Simple compiler includes a multi-strategy duplication detection system:

```
Source Files
    |
    v
[Tokenizer] ──O(N)──> Token Stream
    |                      |
    v                      v
[Karp-Rabin Hash]    [Feature Extraction]    [Doc Extractor]
  exact match          frequency vectors       docstrings
    |                      |                      |
    v                      v                      v
[Group by Hash]      [Cosine Similarity]    [Ollama Embedding]
  O(N)                O(N + U²)              O(N·D) + network
    |                      |                      |
    v                      v                      v
[Exact Groups]       [Fuzzy Groups]        [Semantic Matches]
    |                      |                      |
    +──────────────────────+──────────────────────+
                           |
                           v
                    [Report Generator]
```

---

## Algorithm 1: Karp-Rabin Rolling Hash (Primary)

**File:** `detector.spl` (464 lines)
**Purpose:** Fast exact duplicate detection

### How It Works

1. Tokenize source into `SimpleToken` objects (keyword, identifier, operator, literal)
2. Intern token strings via `TokenInterner` (string → unique integer ID)
3. Slide a window of `min_tokens` size across token stream
4. Compute polynomial rolling hash: `h = (h * 31 + token_id) % 10^9+7`
5. Group windows with identical hashes → duplicate candidates
6. Rank by impact score = `occurrences × lines`

### Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Tokenize | O(N) | O(N) |
| Rolling hash | O(N) per file | O(1) sliding window |
| Group by hash | O(M) hash table | O(M) entries |
| **Total** | **O(N)** | **O(N + M)** |

### Strengths
- Linear time — handles large codebases
- Rolling hash avoids re-computing from scratch per window
- Token interning reduces memory via string deduplication

### Weaknesses
- Exact match only — misses renamed-variable duplicates without identifier normalization
- Hash collisions possible (mitigated by mod 10^9+7)
- Minimum threshold sensitivity (min_tokens=30, min_lines=5)

---

## Algorithm 2: Cosine Similarity (Fuzzy Match)

**File:** `features.spl` (92 lines)
**Purpose:** Detect structural duplicates despite identifier/literal changes

### How It Works

1. **Feature extraction:** Count token frequencies in a code block
2. **Normalization:** `weight = frequency / total_tokens` (TF weighting)
3. **L2 magnitude:** `||v|| = sqrt(sum(weight²))`
4. **Similarity:** `cos(A,B) = (A · B) / (||A|| × ||B||)`
5. **Threshold:** Default ≥ 0.85 = "similar enough"

### Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Feature extraction | O(W) per block | O(U) unique tokens |
| Build vector | O(U) | O(U) |
| Cosine similarity | O(min(U₁,U₂)) | O(1) |
| All comparisons | O(B² × U) | O(B × U) |

Where W=window size, U=unique tokens, B=blocks

### Strengths
- Detects near-duplicates with renamed variables
- Normalized vectors eliminate code length bias
- Configurable threshold

### Weaknesses
- O(B²) pairwise comparisons — capped at `max_blocks_to_analyze=500`
- Loses structural information (bag-of-tokens)
- Cannot detect reordered code

---

## Algorithm 3: Semantic Similarity (LLM-Based)

**Files:** `semantic.spl` (272 lines), `ollama_client.spl`, `embedding_cache.spl`
**Purpose:** Detect semantic duplication via documentation similarity

### How It Works

1. Extract docstrings from functions/classes via AST walk
2. Send docstrings to Ollama API (`nomic-embed-text` model, 768-dim vectors)
3. Cache embeddings in CSV format (`.semantic_cache.txt`)
4. Compute cosine similarity on embedding vectors
5. Classify matches:
   - `copy_paste` (≥0.98): Identical documentation
   - `similar` (≥threshold): Related functionality
   - `drift` (≤drift_threshold): Documentation diverged from similar code

### Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Doc extraction | O(N) AST walk | O(D) docstrings |
| Embedding (remote) | O(D×768) + network | O(D×768) cache |
| Cosine comparison | O(D²×768) | O(1) |

### Fallback: Levenshtein Distance
When Ollama is unavailable: `similarity = 1 - (levenshtein_distance / max_length)`
Complexity: O(L₁×L₂) per pair, O(D²×L²) total

### Strengths
- Semantic understanding beyond tokens
- Detects "same intent, different code" patterns
- Embedding cache reduces API calls

### Weaknesses
- Requires external Ollama service
- Only works for documented code
- Network latency

---

## Algorithm 4: Standalone Checker (run_check.spl)

**File:** `run_check.spl` (~210 lines)
**Purpose:** Lightweight, self-contained duplication detection

### How It Works

1. Collect `.spl` files from target directory
2. Read all files into memory (cached, each read once)
3. For each file, compute combined DJB2 hash over `min_lines` consecutive line windows
4. **Sort** all window hashes using merge sort → O(n log n)
5. Walk sorted array, group consecutive equal hashes
6. **Verify** matches by comparing actual trimmed line content
7. Report cross-file and non-overlapping same-file duplicates

### Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Read files | O(F×L) | O(F×L) cached |
| Hash windows | O(T) total lines | O(W) windows |
| Merge sort | O(W log W) | O(W) |
| Group + verify | O(W + G×K) | O(G) groups |
| **Total** | **O(T + W log W)** | **O(F×L + W)** |

Where F=files, L=lines/file, T=total lines, W=windows, G=groups, K=group size

### Strengths
- No external dependencies (extern fns only)
- O(n log n) vs O(n²) — 100x faster for large inputs
- Content verification eliminates false positives
- File content cached (no re-reads)
- Fast startup (no compiler module loading)

### Weaknesses
- Line-based (not token-based) — comments/whitespace affect results
- DJB2 hash via `rt_text_to_bytes` — simpler than Karp-Rabin
- No identifier normalization
- No cosine/semantic fallback

---

## Supporting Subsystems

### Tokenizer (`tokenizer.spl`)
- Single-pass lexical scanner: O(N)
- Configurable normalization: identifiers, literals, comments, whitespace
- Outputs `SimpleToken(kind, value, line, column)`

### Token Cache (`cache.spl`)
- Hash table: filepath → (mtime, tokens[])
- Timestamp validation: skip re-tokenize if file unchanged
- Lookup: O(1), validation: O(1)

### Incremental Cache (`incremental.spl`)
- File-level result caching in `.duplicate_cache.sdn`
- Config hash invalidation: re-analyze if settings change
- Reduces re-analysis to changed files only

### Embedding Cache (`embedding_cache.spl`)
- Content-hash keyed: re-embed only if docstring content changes
- CSV format for portability
- Hit/miss statistics

---

## External Tools Comparison

| Tool | Approach | Language Support | Complexity | Notes |
|------|----------|-----------------|------------|-------|
| **Simple (detector.spl)** | Token + Karp-Rabin | `.spl` native | O(N) | Self-hosted, integrated |
| **Simple (run_check.spl)** | Line + DJB2 + sort | `.spl` native | O(N log N) | Standalone, no deps |
| **jscpd** | Token hash | Multi (needs mapping) | O(N) | Used with `spl:python` mapping |
| **PMD CPD** | Token-based | Java/C++/etc | O(N log N) | Needs custom lang def |
| **Simian** | Line/token | Multi | O(N log N) | Older, less maintained |
| **CloneDR** | AST-based | Multi | O(N²) | Commercial, semantic |
| **CCFinder** | AST + metrics | Multi | O(N log N) | Academic |

---

## Recommendations

1. **Primary tool:** Use `run_check.spl` for fast, dependency-free scanning
2. **Deep analysis:** Fix `detector.spl` interpreter bugs to enable token-based + cosine similarity
3. **Semantic layer:** Set up Ollama for documentation similarity (optional, high-value for large codebases)
4. **CI integration:** `--max-allowed N` flag for regression prevention
5. **Performance:** Parallel processing (`parallel.spl`) is stubbed — implement with Simple's async/actor system when available
