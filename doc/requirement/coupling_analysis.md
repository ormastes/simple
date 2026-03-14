# Coupling Analysis — Requirement

**Feature:** Static coupling analysis tool for the Simple compiler
**Motivation:** Detect architecture smells, enforce layering rules, and measure module coupling to maintain code quality as the codebase grows (623K+ lines, 2649 files).

---

## Scope

### In Scope

1. **Dependency graph construction** — Build module-level directed graph from import/use statements (extend existing `src/compiler/00.common/dependency/graph.spl`)
2. **Coupling metrics** — Compute per-module:
   - **CBO** (Coupling Between Objects) — count of distinct modules a module depends on
   - **Fan-in** — number of modules that depend on this module
   - **Fan-out** — number of modules this module depends on
   - **RFC** (Response For Class) — count of methods + directly called external methods
   - **Instability (I)** — Fan-out / (Fan-in + Fan-out), range [0,1]
   - **Abstractness (A)** — ratio of abstract types (traits) to total types
   - **Distance from main sequence (D)** — |A + I - 1|
   - **LCOM** (Lack of Cohesion of Methods) — measures how related methods are within a class (LCOM4 variant: connected components in method-field graph)
3. **Public API quality metrics** — Compute per-module/class:
   - **Public Surface Size (PSS)** — count of public methods + public fields
   - **Public Surface Ratio** — public members / total members
   - **External Usage Ratio (EUR)** — externally-used public methods / total public methods (detects dead public surface)
   - **Public API Entropy** — normalized Shannon entropy over external call counts per public method (detects usage imbalance)
   - **API Complexity Index** — weighted composite: PSS + avg param count + overload confusion + (1 - EUR) + entropy
   - **Avg Parameter Count** — average parameters per public method
   - **Max Parameter Count** — maximum parameters on any public method
   - **Overload Confusion** — count of overload groups with similar signatures
4. **Argument Signature Similarity (ATSS)** — Detect function pairs with near-identical parameter type sets:
   - Exact type-set duplicates (edit distance = 0)
   - Near-duplicates (edit distance <= 1, configurable threshold)
   - Extend existing `duplicate_typed_args.spl` with cross-function comparison
   - Lint rule `W0509` for similar signatures
5. **Relaxed Token-Based Duplication** — Enhance existing `duplicate_check/` for structural clones:
   - Token-kind-only mode (`--relaxed`): `x + y * z` matches `a + b * c`
   - Gap tolerance mode (`--gap=N`): allow N non-matching lines within a match (Type-3 clones)
   - Extend `DuplicationConfig` with `relaxed` and `gap_tolerance` fields
   - Lint rule `W0510` for structural code duplication
6. **SCC cycle detection** — Tarjan's algorithm to find strongly connected components (circular dependencies)
4. **DSM (Dependency Structure Matrix)** — N×N matrix output for visualizing module dependencies
5. **Layer violation detection** — Enforce compiler layer ordering (00 < 10 < 15 < 20 < ... < 99), flag backward dependencies
6. **CLI integration** — `bin/simple build coupling` command with options:
   - `--format=text|json|md` — output format
   - `--threshold=N` — flag modules with CBO > N
   - `--layers` — check layer violations only
   - `--dsm` — output DSM matrix
   - `--cycles` — show SCC cycles only
   - `--api` — show public API quality report (PSS, EUR, entropy, complexity index)
   - `--lcom` — show LCOM cohesion report
7. **Lint rules** — New lint rules integrated into `bin/simple build lint`:
   - `W0501` — High CBO (>15 by default)
   - `W0502` — Circular dependency (SCC with >1 member)
   - `W0503` — Layer violation (backward dependency)
   - `W0504` — Unstable module depended on by stable module (instability inversion)
   - `W0505` — High LCOM (low cohesion, class doing too many things)
   - `W0506` — High public surface ratio (>70% public members)
   - `W0507` — Dead public API (EUR < 0.3, most public methods unused externally)
   - `W0508` — API complexity index exceeds threshold

### Out of Scope

- Dynamic coupling analysis (runtime tracing) — future phase
- Semantic/conceptual coupling (LLM embeddings) — future phase
- Centrality / Louvain community detection — future phase
- GUI/visual DSM rendering — future phase (CLI text/markdown only)

---

## I/O Examples

### Example 1: Coupling report (text)
```
$ bin/simple build coupling

=== Coupling Report ===

Module                          CBO  Fan-in  Fan-out  Instab  LCOM  PSS  EUR   Entropy
compiler/00.common/config       3    45      3        0.06    1     8    0.88  0.92
compiler/10.frontend/parser     8    12      8        0.40    2     15   0.73  0.81
compiler/30.types/inference     14   6       14       0.70    1     22   0.64  0.75
compiler/90.tools/depgraph      5    2       5        0.71    3     6    0.50  0.65

WARNING: 2 modules exceed CBO threshold (15):
  compiler/80.driver/pipeline   CBO=18
  compiler/20.hir/lowering      CBO=16

CYCLES: 1 SCC found:
  [compiler/30.types/phase, compiler/25.traits/solver] (2 modules)

LAYER VIOLATIONS: 1 found:
  compiler/10.frontend/desugar -> compiler/20.hir/types (10 -> 20 OK)
  compiler/20.hir/lowering -> compiler/10.frontend/ast (20 -> 10 VIOLATION)
```

### Example 2: Layer violations only
```
$ bin/simple build coupling --layers

=== Layer Violations ===
compiler/20.hir/lowering -> compiler/10.frontend/ast (20 -> 10)
compiler/35.semantics/resolve -> compiler/10.frontend/parser (35 -> 10)

2 violations found.
```

### Example 3: DSM output (markdown)
```
$ bin/simple build coupling --dsm --format=md

| Module    | 00.common | 10.frontend | 20.hir | 30.types |
|-----------|-----------|-------------|--------|----------|
| 00.common |     -     |      0      |   0    |    0     |
| 10.frontend|    5     |      -      |   0    |    0     |
| 20.hir    |    8      |      3      |   -    |    0     |
| 30.types  |    4      |      1      |   6    |    -     |
```

### Example 4: JSON output
```
$ bin/simple build coupling --format=json
{
  "modules": [
    {"name": "compiler/00.common/config", "cbo": 3, "fan_in": 45, "fan_out": 3, "instability": 0.06}
  ],
  "cycles": [["compiler/30.types/phase", "compiler/25.traits/solver"]],
  "layer_violations": [{"from": "compiler/20.hir/lowering", "to": "compiler/10.frontend/ast"}]
}
```

### Example 5: Cycles only
```
$ bin/simple build coupling --cycles

=== Strongly Connected Components ===
SCC #1 (2 modules):
  compiler/30.types/phase
  compiler/25.traits/solver

SCC #2 (3 modules):
  compiler/40.mono/instantiate
  compiler/40.mono/specialize
  compiler/40.mono/resolve

2 SCCs with circular dependencies found.
```

---

## Acceptance Criteria

| ID | Criterion | Priority |
|----|-----------|----------|
| AC-01 | `bin/simple build coupling` produces a coupling report with CBO, fan-in, fan-out, instability per module | Must |
| AC-02 | SCC detection finds all circular dependency cycles using Tarjan's algorithm | Must |
| AC-03 | Layer violation detection flags backward dependencies between numbered compiler layers | Must |
| AC-04 | DSM matrix output shows module-to-module dependency counts | Must |
| AC-05 | RFC metric counts methods + directly called external methods per class/module | Should |
| AC-06 | Instability inversion warning flags stable modules depending on unstable ones | Should |
| AC-07 | JSON and Markdown output formats work alongside default text | Must |
| AC-08 | Lint rules W0501-W0504 integrated into `bin/simple build lint` | Must |
| AC-09 | Threshold configurable via `--threshold=N` flag | Should |
| AC-10 | Performance: analysis completes in <30s for the full Simple compiler codebase | Should |
| AC-11 | Distance from main sequence (D = |A + I - 1|) computed per module | Nice |
| AC-12 | Abstractness (A) metric computed per module | Nice |
| AC-13 | LCOM4 computed per class (connected components in method-field usage graph) | Must |
| AC-14 | Public Surface Size (PSS) and Public Surface Ratio per module/class | Must |
| AC-15 | External Usage Ratio (EUR) detects dead public surface | Should |
| AC-16 | Public API Entropy (normalized Shannon entropy) computed from call-site counts | Should |
| AC-17 | API Complexity Index (weighted composite score) with configurable weights | Should |
| AC-18 | Lint rules W0505-W0508 for LCOM, public surface, dead API, API complexity | Must |
| AC-19 | `--api` flag shows public API quality report separately | Should |
| AC-20 | ATSS detects function pairs with edit distance <= 1 on parameter type sets | Must |
| AC-21 | ATSS threshold configurable via `--atss-threshold=N` | Should |
| AC-22 | Relaxed token duplication mode (`--relaxed`) matches token-kind-only sequences | Must |
| AC-23 | Gap tolerance (`--gap=N`) allows N non-matching lines within a duplicate block | Should |
| AC-24 | Lint rules W0509 (ATSS) and W0510 (structural duplication) integrated | Must |

---

## Dependencies

| Dependency | Path | Status |
|------------|------|--------|
| Import graph | `src/compiler/00.common/dependency/graph.spl` | Exists (extend) |
| Call graph | `src/compiler/10.frontend/core/call_graph.spl` | Exists (use for RFC) |
| Symbol table | `src/compiler/00.common/dependency/symbol.spl` | Exists |
| Visibility | `src/compiler/00.common/dependency/visibility.spl` | Exists |
| Lint infra | `src/compiler/35.semantics/lint/` | Exists (add rules) |
| DepGraph tool | `src/compiler/90.tools/depgraph/` | Exists (extend) |
| Build CLI | `src/app/build/` | Exists (add subcommand) |
| Graph algorithms | `src/lib/common/graph/graph_advanced.spl` | Exists |
| SCC algorithm | `src/lib/common/graph/strongly_connected.spl` | Exists (use directly) |
| Dup typed args lint | `src/compiler/35.semantics/lint/duplicate_typed_args.spl` | Exists (extend for ATSS) |
| Duplicate check tool | `src/app/duplicate_check/` | Exists (extend tokenizer for relaxed mode) |
| Duplicate check tokenizer | `src/app/duplicate_check/tokenizer.spl` | Exists (has ignore_identifiers — enhance) |

---

## Related Documents

- Research: `doc/research/coupling_analysis.md` (Phase 2)
- Plan: `doc/plan/coupling_analysis.md` (Phase 4)
- Design: `doc/design/coupling_analysis.md` (Phase 4)
- System Tests: `test/system/coupling_analysis_spec.spl` (Phase 6)
- Architecture: `doc/architecture/dependency_graphs.md`
