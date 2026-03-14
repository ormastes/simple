# Coupling Analysis — Research

**Related:** [Requirement](../requirement/coupling_analysis.md) | [Plan](../plan/coupling_analysis.md) | [Design](../design/coupling_analysis.md)

---

## 1. Coupling Detection Algorithms — Comprehensive Comparison

### Static Coupling Methods

| Type | What it finds | Algorithm / Metric | Big-O | Real cost (1M LOC) | Industry adoption |
|------|--------------|-------------------|-------|-------------------|-------------------|
| Static | Direct class dependency | **CBO (Coupling Between Objects)** | O(E) | seconds | 5/5 |
| Static | Method call expansion | **RFC (Response for Class)** | O(E) | seconds | 4/5 |
| Static | Import/export deps | **Fan-in / Fan-out** | O(E) | seconds | 5/5 |
| Static | System dep density | **Coupling Factor (CF)** | O(N^2) | seconds | 3/5 |
| Static | Abstract type usage | **Data Abstraction Coupling (DAC)** | O(E) | seconds | 3/5 |
| Static | Indirect dependency | **Transitive dependency (DFS/BFS)** | O(V + E) | seconds-min | 4/5 |
| Static | Architecture cycles | **SCC (Tarjan/Kosaraju)** | O(V + E) | seconds | 5/5 |
| Static | Critical module importance | **Centrality (degree/betweenness)** | O(VE) | seconds-min | 3/5 |
| Static | Subsystem clustering | **Community detection (Louvain)** | O(E log V) | minutes | 2/5 |
| Static | Package instability | **Robert Martin Instability (I)** | O(E) | seconds | 4/5 |
| Static | Layer violations | **Dependency rule checking** | O(E) | seconds | 4/5 |
| Static | Architecture smells | **DSM (Dependency Structure Matrix)** | O(N^2) | seconds-min | 4/5 |

### Dynamic Coupling Methods

| Type | What it finds | Algorithm / Metric | Big-O | Real cost | Industry |
|------|--------------|-------------------|-------|-----------|----------|
| Dynamic | Runtime method interaction | **DCM (Dynamic Message Coupling)** | O(trace) | min-hours | 2/5 |
| Dynamic | Object collaboration graph | **Runtime interaction graph** | O(trace) | min-hours | 2/5 |
| Dynamic | Runtime call weight | **Call frequency weighting** | O(trace) | min-hours | 2/5 |
| Dynamic | Dynamic import/export | **ICP / ECP metrics** | O(trace) | min-hours | 2/5 |
| Dynamic | Polymorphic resolution | **Runtime call graph analysis** | O(trace) | min-hours | 3/5 |
| Dynamic | Component communication | **Event tracing graphs** | O(trace) | hours | 2/5 |

Trace size: `trace_size ~ number_of_calls` (10M-1B events for large systems). Dynamic analysis expensive due to instrumentation overhead.

### Semantic / Conceptual Coupling

| Type | What it finds | Algorithm / Metric | Big-O | Real cost | Industry |
|------|--------------|-------------------|-------|-----------|----------|
| Semantic | Similar concept modules | **CCBO** | O(N^2) | min-hours | 1/5 |
| Semantic | Topic related classes | **LSA / LDA** | O(N^2) | min-hours | 1/5 |
| Semantic | Identifier similarity | **TF-IDF cosine** | O(N^2) | minutes | 2/5 |
| Semantic | Embedding similarity | **BERT/LLM embeddings** | O(N^2) | hours | 1/5 |

---

## 2. LCOM (Lack of Cohesion of Methods)

### Variants

| Variant | Definition | Weakness |
|---------|-----------|----------|
| LCOM1 (CK) | P - Q where P = method pairs not sharing fields, Q = pairs sharing fields | Can be negative, hard to interpret |
| LCOM2 (Henderson-Sellers) | (avg(m(A)) - M) / (1 - M) where m(A) = methods accessing attribute A | Better normalized [0,1] |
| LCOM3 | Number of connected components in method-attribute graph | Integer, intuitive |
| **LCOM4** | Connected components in method-method+method-field graph (includes method calls) | **Best practical choice** |
| LCOM5 | (a - kl) / (l - kl) where a = field accesses, k = fields, l = methods | Continuous [0,1] |

### LCOM4 Algorithm (Recommended)

```
For class C with methods M1..Mn and fields F1..Fk:

1. Build undirected graph G:
   - Nodes = {M1..Mn}
   - Edge (Mi, Mj) if:
     a) Mi and Mj both access some field Fk, OR
     b) Mi calls Mj (or vice versa)

2. LCOM4 = number of connected components in G

Interpretation:
  LCOM4 = 1  → cohesive class (all methods related)
  LCOM4 = 2  → class should maybe be split into 2
  LCOM4 = N  → class doing N unrelated things
```

**Complexity:** O(M + F) per class where M = methods, F = fields. Uses union-find for efficient connected components.

### Why LCOM4

- LCOM1 produces negative values, unintuitive
- LCOM2/5 are normalized but miss method-to-method calls
- LCOM3 is close but only considers field access, not method calls
- **LCOM4 captures both field-sharing and internal method calls** — most accurate cohesion picture
- Used by tools: Structure101, NDepend, CppDepend

---

## 3. Public API Entropy and API Complexity

### Background

"Public API entropy" and "API complexity index" are **not canonical OO metrics** like CBO/RFC/WMC/MHF. They are **custom composite metrics** built from standard structural measurements. Research on API usability (Rama & Kak, Purdue) proposes structural API metrics as **relative/comparative indicators**, not universal absolute scores.

### Public API Entropy Definition

```
For class/module C:

let public methods = m1..mk
let ui = external call count of method mi (from other modules)
let U = sum(ui)
let pi = ui / U

API_Entropy(C) = -sum(pi * log2(pi))
Normalized_API_Entropy(C) = API_Entropy(C) / log2(k)    # range [0,1]
```

**Interpretation:**
- **Low entropy (< 0.3):** Few methods dominate usage → likely too many rarely-used public methods (API bloat)
- **High entropy (> 0.8):** Usage spread evenly → either well-designed broad API or hard-to-learn API
- **Use as ranking signal**, not absolute threshold

**Edge cases:**
- k = 0 or k = 1: entropy = 0 (trivially)
- All ui = 0 (no external callers): EUR = 0, entropy undefined → report as "no external usage"

### API Complexity Index

Weighted composite score:

```
API_Complexity_Index(C) =
  w1 * zscore(PublicMethodCount)        # raw size
+ w2 * zscore(AvgParameterCount)        # parameter complexity
+ w3 * zscore(OverloadConfusion)        # similar-signature confusion
+ w4 * zscore(1 - EUR)                  # dead public surface
+ w5 * zscore(1 - NormalizedEntropy)    # usage imbalance
```

**Default weights:** w1=0.3, w2=0.2, w3=0.1, w4=0.2, w5=0.2

**Ingredients from API usability research (Rama & Kak):**
- **APXI:** parameter-list complexity
- **AMNOI:** overload issues
- **AMNCI:** confusing method names
- **AMGI:** poor grouping
- **AESI:** exception specificity
- **ADI:** documentation index

For Simple, we focus on: PSS, param count, overloads, EUR, entropy.

### Practical Three-Number Summary

For each class/module, report:

| Metric | What | Why |
|--------|------|-----|
| **PSS** (Public Surface Size) | public methods + public fields | Raw API size |
| **EUR** (External Usage Ratio) | externally-used / total public | Dead surface detection |
| **Normalized Entropy** | Shannon entropy of usage distribution | Usage balance |

### Implementation Phases

**Phase A: Static core (cheap, O(P) per class)**
- Public method/field count (PSS)
- Public/total ratio
- Avg/max parameter count
- Overload group count
- LCOM4

**Phase B: Static + usage enrichment (O(call_sites) total)**
- External callers per public method
- EUR
- Normalized entropy
- API Complexity Index

**Phase C: Dynamic refinement (future, O(trace))**
- Runtime-weighted entropy from execution traces
- Hot subsystem analysis only

### Strengths and Limitations

**Entropy detects:**
- Classes with many public methods where few are used (kitchen sink)
- Historically grown APIs with accumulated clutter
- Framework objects with broad, weakly-focused surfaces

**Entropy is weak at:**
- Distinguishing well-designed broad APIs from bad ones
- Understanding semantics
- Handling sparse usage in libraries with many legitimate edge-case methods

**Recommendation:** Use as **relative ranking signal** to find classes whose public surface is too large or weakly justified. Not as universal threshold.

---

## 4. Graph Analysis Algorithms

| Purpose | Algorithm | Big-O | Notes |
|---------|-----------|-------|-------|
| Cycle detection | **Tarjan SCC** | O(V + E) | Single DFS pass, stack-based |
| Reachability | DFS/BFS | O(V + E) | Standard |
| Central component | Betweenness centrality | O(VE) | Future phase |
| Architecture clustering | Louvain | O(E log V) | Future phase |
| Impact analysis | Transitive closure | O(V(V+E)) | Future phase |

### Tarjan's SCC Algorithm

```
index = 0
stack = []
result = []

fn strongconnect(v):
    v.index = index
    v.lowlink = index
    index += 1
    stack.push(v)
    v.on_stack = true

    for each edge (v, w):
        if w.index is undefined:
            strongconnect(w)
            v.lowlink = min(v.lowlink, w.lowlink)
        else if w.on_stack:
            v.lowlink = min(v.lowlink, w.index)

    if v.lowlink == v.index:
        scc = []
        repeat:
            w = stack.pop()
            w.on_stack = false
            scc.push(w)
        until w == v
        result.push(scc)

for each vertex v:
    if v.index is undefined:
        strongconnect(v)
```

**Properties:** O(V + E) time, O(V) space, finds all SCCs in one pass.

---

## 5. DSM (Dependency Structure Matrix)

### What it is

N×N matrix where cell (i,j) = number of dependencies from module i to module j. Upper triangle = forward deps (OK), lower triangle = backward deps (violations in layered architectures).

### Layer-Ordered DSM

For the Simple compiler with numbered layers (00, 10, 15, 20, ...):
- Sort modules by layer number
- Ideal: all dependencies in upper-right triangle (lower layer depends on nothing above it)
- Any cell in lower-left triangle = layer violation

### Partitioned DSM

After SCC detection, group SCC members together. This reveals:
- Which SCCs cause the most cross-cutting dependencies
- Where to break cycles

---

## 6. What Exists in the Codebase

| Component | Path | Status | Use for |
|-----------|------|--------|---------|
| Import graph | `src/compiler/00.common/dependency/graph.spl` | Exists | Adjacency list, DFS cycle detection — extend with SCC, metrics |
| Call graph | `src/compiler/10.frontend/core/call_graph.spl` | Exists | Recursion detection — use for RFC, LCOM |
| Symbol table | `src/compiler/00.common/dependency/symbol.spl` | Exists | Cross-module symbol tracking |
| Visibility | `src/compiler/00.common/dependency/visibility.spl` | Exists | 4-level visibility hierarchy |
| DepGraph tool | `src/compiler/90.tools/depgraph/` | Exists | Dependency graph generator — extend |
| Symbol analyzer | `src/compiler/90.tools/symbol_analyzer.spl` | Exists | Transitive deps — extend for metrics |
| Graph algorithms | `src/lib/common/graph/graph_advanced.spl` | Exists | All paths, DAG — add SCC |
| Lint infra | `src/compiler/35.semantics/lint/` | Exists | lint_module, lint_star_import, lint_wide_public — add coupling rules |
| Build metrics | `src/compiler/80.driver/build/metrics.spl` | Exists | Timing/size — add coupling metrics |

### Key Lint Rules Already Present

- `W0404` — Wide public API (>30 exports) — **directly related to PSS**
- `W0406` — Star import detection
- `XREF001-004` — Cross-reference validation

---

## 7. Industry Tool Comparison

### What tools compute internally

| Tool | Metrics | Algorithm |
|------|---------|-----------|
| **CppDepend/NDepend** | CBO, RFC, LCOM, DSM, instability, abstractness, type/method coupling | AST + symbol resolution |
| **Structure101** | DSM, SCC, layer violations, fat/tangle metrics | Bytecode/AST analysis |
| **SonarQube** | Cognitive complexity, file coupling, circular deps | AST analysis |
| **Understand (SciTools)** | CBO, RFC, LCOM, WMC, DIT, NOC, fan-in/out | Multi-language AST |
| **JArchitect** | All CK metrics + DSM + dependency rules | Bytecode analysis |

### Standard Pipeline (All Tools)

```
source code
   ↓
AST / symbol table
   ↓
dependency graph (V,E)
   ↓
metrics (CBO, fan-in/out, SCC, instability, LCOM)
   ↓
rules (layer violations, thresholds, instability inversion)
   ↓
report (text, HTML, JSON)
```

### Performance Benchmarks (Real)

For 1M LOC, 20k classes, 200k dependencies:

| Step | Time |
|------|------|
| Dependency extraction | 10-60s |
| Coupling metrics (CBO, fan-in/out) | <1s |
| SCC detection | <1s |
| LCOM4 computation | <1s |
| DSM construction | 1-5s |
| API entropy (with call-site scan) | 5-30s |
| Centrality (future) | 10-30s |

**For Simple compiler (~2600 files, ~623K lines):** All static metrics should complete in <10s.

---

## 8. Argument Signature Similarity Detection

### Problem

Functions with nearly-identical parameter type sets are a coupling smell and a source of bugs:
- **Swappable args:** `fn draw(x: i64, y: i64)` — already caught by existing `duplicate_typed_args.spl` (DTYP001)
- **Near-duplicate signatures:** Two functions `fn foo(a: Text, b: Int, c: Bool)` and `fn bar(a: Text, b: Int)` differ by one parameter — likely candidates for refactoring into a shared interface

### What to detect

**Argument Type Set Similarity (ATSS):** Given two functions f and g, compare their parameter type multisets.

```
TypeSet(f) = multiset of parameter types (ignoring names)
TypeSet(g) = multiset of parameter types

Similarity = 1 - EditDistance(TypeSet(f), TypeSet(g)) / max(|TypeSet(f)|, |TypeSet(g)|)

Where EditDistance = number of single-element additions or removals to transform one into the other
```

**Detection rule:** Flag function pairs where:
- `EditDistance(TypeSet(f), TypeSet(g)) <= threshold` (default: 1)
- AND both functions are in the same module or closely related modules
- AND the functions are not trivially related (constructor/factory pattern excluded)

### Algorithm: Sorted Type Vector + Edit Distance

```
For each function f:
  1. Extract param types as sorted vector: TypeVec(f) = sort([type1, type2, ...])
  2. Hash the sorted vector for fast exact-match grouping

Phase 1: Exact match groups (O(N) with hash)
  Group functions by identical TypeVec → these share exact type signatures

Phase 2: Near-match detection (threshold = 1 edit)
  For each function f:
    Generate all 1-deletion variants of TypeVec(f):
      for i in 0..len(TypeVec(f)):
        variant = TypeVec(f) with element i removed
        hash variant → lookup in deletion index
    If any variant matches another function's TypeVec or deletion variant → flag

  Complexity: O(N * K) where N = functions, K = avg params per function
  For K typically 2-5, this is effectively O(N)
```

### Alternative: Jaccard Similarity on Type Sets

```
Jaccard(f, g) = |TypeSet(f) ∩ TypeSet(g)| / |TypeSet(f) ∪ TypeSet(g)|

Flag pairs where Jaccard >= 0.8 (configurable)
```

Simpler but less precise than edit distance for ordered signatures.

### Practical Thresholds

| Threshold | What it catches | False positive rate |
|-----------|----------------|-------------------|
| EditDist = 0 | Exact type signature duplicates | Very low |
| EditDist = 1 | One param added/removed/changed | Low-moderate |
| EditDist = 2 | Two params different | Moderate-high |
| Jaccard >= 0.9 | Very similar | Low |
| Jaccard >= 0.7 | Somewhat similar | High |

**Recommendation:** Default `EditDist <= 1` for warnings. This catches:
- Functions that are clearly related but differ by one optional parameter
- Copy-paste functions where one param was added
- Functions that should share a common base type/trait

### Integration with Existing Infrastructure

The codebase already has `duplicate_typed_args.spl` which:
- Collects function definitions with `{fn_name: [{name, type}]}` registry
- Groups params by type string
- O(n) via type-string grouping

**Extend this to cross-function comparison:**
1. Reuse the param type registry from DTYP001
2. Add a second pass comparing TypeVecs across functions
3. New lint rule: `W0509` — Similar function signatures (ATSS)

### What Existing Tools Do

| Tool | Feature | Algorithm |
|------|---------|-----------|
| **PMD** (Java) | CPD with method-signature comparison | Token hash |
| **SonarQube** | Cognitive complexity + method similarity | AST comparison |
| **IntelliJ IDEA** | "Similar method" inspection | Structural search |
| **Simian** | Parameterized clone detection | Line hash + normalization |

None of these do type-set edit distance specifically — this would be a novel lint check.

---

## 9. Relaxed Token-Based Line Duplication Detection

### Problem

Standard token-based duplication (like jscpd) requires **exact** token matches. But many real duplicates differ only in variable/function names:

```simple
# These are structural duplicates:
val total = items.map(\x: x.price).sum()
val count = entries.map(\e: e.value).sum()

# Token kinds match perfectly:
# KEYWORD IDENT OP IDENT DOT IDENT LPAREN LAMBDA IDENT COLON IDENT DOT IDENT RPAREN DOT IDENT LPAREN RPAREN
```

### Existing Infrastructure

The `duplicate_check/tokenizer.spl` already has:
- `ignore_identifiers` flag → normalizes all identifiers to `"IDENTIFIER"`
- `ignore_literals` flag → normalizes all literals to `"LITERAL"`
- `SimpleTokenKind` enum: `Identifier`, `Keyword`, `Operator`, `Literal`, `Punctuation`, `Comment`, `Whitespace`

**This is exactly the relaxed token comparison the user wants!** The `ignore_identifiers` mode already does "same kind of tokens, variable names differ" matching.

### What To Enhance

The existing system works but can be improved:

#### A. Token Kind Sequence Hashing (Current Approach, Enhanced)

```
Current: tokenize → normalize identifiers → hash token sequences → compare

Enhanced: tokenize → normalize to token-kind-only sequence → rolling hash → suffix array comparison

Token-kind-only sequence example:
  "val total = items.map(\x: x.price)" →
  [KW, ID, OP, ID, PUNCT, ID, LPAREN, LAMBDA, ID, COLON, ID, PUNCT, ID, RPAREN]
```

**Key insight:** Instead of hashing the full normalized token string, hash **only the token kind sequence**. This is more aggressive normalization — even keyword differences within the same kind are ignored.

#### B. Parameterized Clone Detection (Type-2 Clones)

Research literature defines clone types:

| Type | Definition | Example |
|------|-----------|---------|
| Type-1 | Exact copy (ignoring whitespace/comments) | Identical code |
| Type-2 | Renamed identifiers/literals (structural match) | `x+y` vs `a+b` |
| Type-3 | Small edits (added/removed/modified statements) | Type-2 + gap tolerance |
| Type-4 | Semantic equivalence (different structure, same behavior) | Loop vs recursion |

**The existing `ignore_identifiers` mode does Type-2 detection.** What's missing:

1. **Type-3 with gap tolerance** — allow N non-matching lines within a match
2. **Finer token-kind granularity** — distinguish `fn` keyword from `if` keyword (currently both `Keyword`)
3. **Structural normalization** — `a + b` and `b + a` for commutative ops

#### C. Optimized Algorithm: Suffix Array + LCP

The most efficient algorithm for finding all duplicate token-kind subsequences:

```
1. Tokenize all files → unified token-kind sequence S (with file/line markers)
2. Build suffix array SA of S: O(N)
3. Build LCP (Longest Common Prefix) array: O(N)
4. Scan LCP array for entries >= min_length threshold
5. Group by cluster → report duplicate groups

Total: O(N log N) or O(N) with SA-IS algorithm
Where N = total tokens across all files
```

**vs. Current approach (likely hash-based):**
- Hash-based: O(N * W) where W = window size, O(N) space for hash table
- Suffix array: O(N) time, O(N) space, finds ALL maximal duplicates

**Suffix array is theoretically optimal** but more complex to implement. Hash-based with rolling hash (Rabin-Karp) is simpler and practical.

#### D. Rolling Hash (Rabin-Karp) for Token-Kind Sequences

```
1. Tokenize → token-kind sequence
2. For each file, compute rolling hash over windows of size W:
   hash(i) = sum(token_kind[i+j] * base^j) mod prime, for j in 0..W
3. Store all hashes in hash map: hash → [(file, line)]
4. Collisions → compare full token-kind sequences
5. Extend matches greedily beyond window

Complexity: O(N * W) worst case, O(N) expected with good hash
```

### Comparison of Approaches

| Approach | Complexity | Finds Type-2 | Finds Type-3 | Implementation |
|----------|-----------|-------------|-------------|---------------|
| Current (token hash with ignore_identifiers) | O(N*W) | Yes | No | Exists |
| Token-kind-only hash | O(N*W) | Yes (stricter) | No | Small change |
| Suffix array + LCP | O(N) | Yes | Partial | Complex |
| Rolling hash (Rabin-Karp) on token kinds | O(N) expected | Yes | No | Moderate |
| AST-based structural comparison | O(N^2) | Yes | Yes | Complex |

### Recommendation

**Enhance existing `duplicate_check/` with two modes:**

1. **`--relaxed` mode (token-kind-only):** Normalize to token kind sequence only (not token value). This is a one-line change in the tokenizer — instead of `"IDENTIFIER"`, emit just the kind enum ordinal. Catches more duplicates than `ignore_identifiers` because even different keywords of the same kind match.

2. **`--gap=N` mode (Type-3 tolerance):** Allow up to N non-matching lines within a matching block. Algorithm:
   ```
   For each candidate match:
     extend greedily, allowing up to gap_tolerance non-matching lines
     report if total matching lines >= min_lines
   ```

### Performance for Simple Compiler

```
~623K lines → ~2M tokens (estimated 3 tokens/line average)
Window size W = 30 tokens (default min_tokens)

Token-kind hash:     O(2M) = ~1s
Suffix array:        O(2M) = ~1s
Full AST comparison: O(4T) = too slow
```

Both token-kind hash and suffix array are practical. Recommend starting with token-kind hash (minimal change to existing code), upgrade to suffix array later if needed.

### Integration

- Extend `DuplicationConfig` with `relaxed: bool` and `gap_tolerance: i64`
- In tokenizer: when `relaxed`, emit token kind ordinal instead of normalized value
- In detector: when `gap_tolerance > 0`, extend match windows with gap allowance
- New lint rule: `W0510` — Structural code duplication (relaxed token match)

---

## 10. Recommendations for Implementation

### Priority Order

1. **Fan-in / Fan-out / CBO** — simplest, most useful, O(E)
2. **SCC (Tarjan)** — critical for cycle detection, O(V+E) — `strongly_connected.spl` already exists in graph lib
3. **Layer violations** — specific to Simple's numbered layers, O(E)
4. **Instability + Distance** — Robert Martin metrics, O(E)
5. **LCOM4** — cohesion per class, O(M+F) per class
6. **DSM** — matrix output, O(N^2)
7. **PSS + Public Surface Ratio** — API size metrics, O(P)
8. **EUR + Entropy** — requires call-site scanning, O(call_sites)
9. **API Complexity Index** — weighted composite, computed from above
10. **RFC** — requires call graph, O(E)
11. **Arg Signature Similarity (ATSS)** — cross-function type-set comparison, O(N*K) — extends existing `duplicate_typed_args.spl`
12. **Relaxed Token Duplication** — token-kind-only matching, O(N) — extends existing `duplicate_check/` with `ignore_identifiers`

### Architecture Decision

**Extend existing infrastructure** rather than building from scratch:
- `graph.spl` already has adjacency list + DFS → add Tarjan SCC + metric computation
- `depgraph/` already generates dep graphs → add metric reporting
- Lint infra already has module-level rules → add W0501-W0508
- Build CLI already has subcommands → add `coupling`

### Risk: Call-site scanning for EUR/Entropy

Scanning all call sites to compute external usage requires either:
- A post-resolution pass over all resolved call expressions (preferred — compiler already resolves)
- A separate grep-like scan (fallback — slower, less accurate)

**Recommendation:** Hook into the compiler's name resolution phase to collect call-site data during normal compilation.

---

## References

- Chidamber & Kemerer (1994): CK metrics (CBO, RFC, LCOM, WMC, DIT, NOC)
- Robert C. Martin (2003): Instability, Abstractness, Distance from Main Sequence
- Tarjan (1972): Strongly connected components algorithm
- Henderson-Sellers (1996): LCOM variants
- Rama & Kak (Purdue): API usability structural metrics (APXI, AMNOI, AMNCI, AMGI, AESI, ADI)
- Steward (1981): Dependency Structure Matrix (DSM)
- Roy & Cordy (2007): Clone detection taxonomy (Type 1-4 classification)
- Koschke (2007): Suffix tree/array approaches for clone detection
- Kamiya et al. (2002): CCFinder — parameterized token matching
- Baker (1995): Parameterized duplication detection via p-strings
