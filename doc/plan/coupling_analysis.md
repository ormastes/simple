# Coupling Analysis — Plan

**Related:** [Requirement](../requirement/coupling_analysis.md) | [Research](../research/coupling_analysis.md) | [Design](../design/coupling_analysis.md)

## Objective

Build a comprehensive static coupling analysis tool integrated into `bin/simple build coupling` and `bin/simple build lint`. Provides CBO, fan-in/out, instability, LCOM4, SCC cycle detection, DSM, layer violations, public API quality metrics (PSS, EUR, entropy), argument signature similarity (ATSS), and relaxed token-based duplication detection. All metrics computed from existing AST/symbol infrastructure in <30s for the full codebase.

## Current Status

| Component | Status | Evidence |
|-----------|--------|----------|
| Import graph (adjacency list, DFS) | Real | `src/compiler/00.common/dependency/graph.spl` |
| Call graph (recursion detection) | Real | `src/compiler/10.frontend/core/call_graph.spl` |
| Symbol table (cross-module tracking) | Real | `src/compiler/00.common/dependency/symbol.spl` |
| Visibility (4-level hierarchy) | Real | `src/compiler/00.common/dependency/visibility.spl` |
| DepGraph tool (generator, analyzer) | Real | `src/compiler/90.tools/depgraph/` |
| SCC algorithm | Real | `src/lib/common/graph/strongly_connected.spl` |
| Lint infra (15+ rules, __init__.spl registry) | Real | `src/compiler/35.semantics/lint/` |
| Duplicate typed args (DTYP001) | Real | `src/compiler/35.semantics/lint/duplicate_typed_args.spl` |
| Duplicate check (tokenizer, detector, semantic) | Real | `src/app/duplicate_check/` (17 files) |
| Wide public lint (W0404, >30 exports) | Real | `src/compiler/35.semantics/lint/wide_public.spl` |
| Build metrics (timing/size) | Real | `src/compiler/80.driver/build/metrics.spl` |
| Coupling metrics module | Missing | Need new `src/compiler/90.tools/coupling/` |
| Coupling CLI subcommand | Missing | Need new `coupling` in build CLI |
| LCOM4 computation | Missing | Need new pass over class definitions |
| API quality metrics (PSS, EUR, entropy) | Missing | Need call-site scanning |
| ATSS cross-function comparison | Missing | Extend `duplicate_typed_args.spl` |
| Relaxed token duplication | Partial | `ignore_identifiers` exists, need token-kind-only mode |
| Lint rules W0501-W0510 | Missing | Need 10 new lint rules |

## What To Do

### Task Group A: Core Graph Metrics (difficulty: 2)

**1. Build module dependency graph from AST** (difficulty: 2)
- Extend `src/compiler/00.common/dependency/graph.spl` with metric computation methods
- Add `fan_in(module)`, `fan_out(module)`, `cbo(module)` methods to ImportGraph
- Fan-in = in-degree, fan-out = out-degree, CBO = fan-out (distinct modules)

**2. Integrate SCC from graph library** (difficulty: 1)
- Wire existing `src/lib/common/graph/strongly_connected.spl` into coupling analyzer
- Convert ImportGraph adjacency list to format expected by SCC algorithm
- Filter SCCs to only report components with >1 member (cycles)

**3. Layer violation detection** (difficulty: 2)
- Parse layer numbers from compiler directory names (00, 10, 15, 20, ...)
- For each edge in dependency graph, check if source layer > target layer
- Report violations with source → target and layer numbers

**4. Instability and Distance metrics** (difficulty: 2)
- Instability I = fan-out / (fan-in + fan-out), range [0,1]
- Abstractness A = trait_count / total_type_count per module
- Distance D = |A + I - 1|
- Instability inversion: warn if stable module (low I) depends on unstable module (high I)

### Task Group B: Cohesion & API Quality (difficulty: 3)

**5. LCOM4 computation** (difficulty: 3)
- For each class: build undirected graph of methods
- Edge if two methods share a field access OR one calls the other
- LCOM4 = connected components count (union-find)
- Requires walking class method bodies for field access and method call patterns

**6. Public Surface Size and Ratio** (difficulty: 2)
- Count public methods + public fields per class/module
- PSS = public_methods + public_fields
- Ratio = PSS / total_members
- Leverage existing visibility system from `visibility.spl`

**7. External Usage Ratio (EUR)** (difficulty: 3)
- Scan all call expressions across codebase
- For each public method: count external callers (from other modules)
- EUR = externally_used_public_methods / total_public_methods
- Requires post-resolution pass (hook into name resolution data)

**8. Public API Entropy** (difficulty: 2)
- From EUR call-site counts: compute normalized Shannon entropy
- `entropy = -sum(pi * log2(pi)) / log2(k)` where pi = usage_i / total_usage
- Handle edge cases: k=0, k=1, all-zero usage

**9. API Complexity Index** (difficulty: 2)
- Weighted composite: PSS + avg_param_count + overload_confusion + (1-EUR) + (1-entropy)
- Z-score normalization across all modules
- Configurable weights (default: 0.3, 0.2, 0.1, 0.2, 0.2)

### Task Group C: Signature & Duplication Detection (difficulty: 3)

**10. Argument Signature Similarity (ATSS)** (difficulty: 3)
- Extend `duplicate_typed_args.spl` with cross-function type-set comparison
- Extract sorted type vectors per function
- Phase 1: hash exact type vectors → group identical signatures
- Phase 2: generate 1-deletion variants → detect near-duplicates (edit distance = 1)
- Configurable threshold (default: 1)

**11. Relaxed token-kind duplication mode** (difficulty: 2)
- Extend `duplicate_check/tokenizer.spl`: when `relaxed=true`, emit token kind ordinal only
- `x + y * z` → `[ID, OP, ID, OP, ID]` matches `a + b * c` → `[ID, OP, ID, OP, ID]`
- Existing rolling hash / comparison logic works unchanged on normalized tokens

**12. Gap-tolerant duplication (Type-3)** (difficulty: 3)
- Extend duplicate detector: when `gap_tolerance > 0`, extend matches allowing N non-matching lines
- Algorithm: greedy match extension with gap budget
- Report total matching lines vs gap lines in each duplicate group

### Task Group D: DSM & Reporting (difficulty: 2)

**13. DSM matrix construction** (difficulty: 2)
- N×N matrix where cell (i,j) = dependency count from module i to module j
- Sort by layer number for compiler modules
- Output formats: text table, markdown table, JSON

**14. CLI subcommand `bin/simple build coupling`** (difficulty: 2)
- Parse flags: `--format=text|json|md`, `--threshold=N`, `--layers`, `--dsm`, `--cycles`, `--api`, `--lcom`, `--relaxed`, `--gap=N`, `--atss-threshold=N`
- Dispatch to appropriate metric computations
- Format and print results

**15. Report formatter** (difficulty: 2)
- Text format: tabular report with warnings
- JSON format: structured output for tooling
- Markdown format: for documentation/CI integration

### Task Group E: Lint Integration (difficulty: 2)

**16. Lint rules W0501-W0510** (difficulty: 2)
- W0501: High CBO (>15 default)
- W0502: Circular dependency (SCC >1 member)
- W0503: Layer violation (backward dependency)
- W0504: Instability inversion
- W0505: High LCOM (>3 default)
- W0506: High public surface ratio (>0.7 default)
- W0507: Dead public API (EUR < 0.3 default)
- W0508: High API complexity index
- W0509: Similar function signatures (ATSS, edit distance <= 1)
- W0510: Structural code duplication (relaxed token match)

**17. Register lint rules in `__init__.spl`** (difficulty: 1)
- Add re-exports for new coupling lint rules
- Follow existing pattern from other lint rules

### Task Dependencies (DAG)

```
1 (graph metrics) ──┬──→ 2 (SCC) ──→ 13 (DSM)
                    ├──→ 3 (layer violations)
                    ├──→ 4 (instability) ──→ 9 (API complexity)
                    │
5 (LCOM4)          ├──→ 6 (PSS) ──→ 7 (EUR) ──→ 8 (entropy) ──→ 9
                    │
10 (ATSS)          │    (independent)
11 (relaxed dup)   │    (independent)
12 (gap tolerance) │    (depends on 11)
                    │
                    └──→ 13 (DSM)
                         14 (CLI) ← all metrics
                         15 (formatter) ← 14
                         16 (lint rules) ← all metrics
                         17 (register) ← 16
```

### Parallelization

Three independent workstreams:
- **Stream 1:** Tasks 1→2→3→4→13 (graph metrics, SCC, layers, instability, DSM)
- **Stream 2:** Tasks 5→6→7→8→9 (LCOM, PSS, EUR, entropy, API complexity)
- **Stream 3:** Tasks 10, 11→12 (ATSS, relaxed duplication)
- **Merge:** Tasks 14→15→16→17 (CLI, formatter, lint rules, registration)

## Model Assignment

| Task | Difficulty | Model |
|------|-----------|-------|
| 1 (graph metrics) | 2 | sonnet |
| 2 (SCC integration) | 1 | haiku |
| 3 (layer violations) | 2 | sonnet |
| 4 (instability) | 2 | sonnet |
| 5 (LCOM4) | 3 | sonnet |
| 6 (PSS) | 2 | sonnet |
| 7 (EUR) | 3 | sonnet |
| 8 (entropy) | 2 | sonnet |
| 9 (API complexity) | 2 | sonnet |
| 10 (ATSS) | 3 | sonnet |
| 11 (relaxed dup) | 2 | sonnet |
| 12 (gap tolerance) | 3 | sonnet |
| 13 (DSM) | 2 | sonnet |
| 14 (CLI) | 2 | sonnet |
| 15 (formatter) | 2 | sonnet |
| 16 (lint rules) | 2 | sonnet |
| 17 (register) | 1 | haiku |

## File Plan

### New Files

| File | Purpose |
|------|---------|
| `src/compiler/90.tools/coupling/__init__.spl` | Module init, re-exports |
| `src/compiler/90.tools/coupling/metrics.spl` | CBO, fan-in/out, instability, distance |
| `src/compiler/90.tools/coupling/lcom.spl` | LCOM4 computation |
| `src/compiler/90.tools/coupling/api_quality.spl` | PSS, EUR, entropy, API complexity index |
| `src/compiler/90.tools/coupling/dsm.spl` | Dependency Structure Matrix |
| `src/compiler/90.tools/coupling/layer_check.spl` | Layer violation detection |
| `src/compiler/90.tools/coupling/atss.spl` | Argument Type Set Similarity |
| `src/compiler/90.tools/coupling/report.spl` | Text/JSON/MD formatting |
| `src/compiler/90.tools/coupling/main.spl` | CLI entry point for `build coupling` |
| `src/compiler/35.semantics/lint/coupling.spl` | Lint rules W0501-W0510 |
| `test/system/coupling_analysis_spec.spl` | System tests |

### Files to Modify

| File | Change |
|------|--------|
| `src/compiler/00.common/dependency/graph.spl` | Add fan_in/fan_out/cbo methods |
| `src/compiler/35.semantics/lint/__init__.spl` | Re-export coupling lint rules |
| `src/compiler/35.semantics/lint/duplicate_typed_args.spl` | Add ATSS cross-function comparison |
| `src/app/duplicate_check/tokenizer.spl` | Add relaxed token-kind-only mode |
| `src/app/duplicate_check/config.spl` | Add `relaxed`, `gap_tolerance` fields |
| `src/app/duplicate_check/detector.spl` | Add gap-tolerant matching |

## Estimated Effort

- **Total tasks:** 17
- **Total difficulty points:** 37
- **Estimated implementation time:** 3 streams in parallel
  - Stream 1 (graph/SCC/layers/instability/DSM): 5 tasks, difficulty 9
  - Stream 2 (LCOM/PSS/EUR/entropy/API): 5 tasks, difficulty 12
  - Stream 3 (ATSS/relaxed/gap): 3 tasks, difficulty 8
  - Merge (CLI/formatter/lint/register): 4 tasks, difficulty 7
