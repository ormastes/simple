# Coupling Analysis — Design

**Related:** [Requirement](../requirement/coupling_analysis.md) | [Research](../research/coupling_analysis.md) | [Plan](../plan/coupling_analysis.md) | [Tests](../../test/system/coupling_analysis_spec.spl)

---

## 1. Module Structure

```
src/compiler/90.tools/coupling/
  __init__.spl            # Module declaration, child mods, all re-exports
  metrics.spl             # CBO, fan-in/out, instability, abstractness, distance, SCC cycles
  layer_check.spl         # Compiler layer ordering enforcement (00 < 10 < ... < 99)
  dsm.spl                 # Dependency Structure Matrix (N x N) construction + formatting
  lcom.spl                # LCOM4 cohesion via union-find on method-field graph
  api_quality.spl         # PSS, EUR, entropy, API complexity index
  atss.spl                # Argument Type Set Similarity (cross-function type-set comparison)
  relaxed_tokenizer.spl   # Token-kind-only normalization for structural duplication
  gap_matcher.spl         # Gap-tolerant matching on relaxed token streams
  report.spl              # Text / JSON / Markdown report formatters
  main.spl                # CLI entry point, arg parsing, orchestration
```

All public types and functions are re-exported through `__init__.spl`. Consumers import from `compiler.tools.coupling.*` without reaching into child modules directly.

---

## 2. Type Definitions

### metrics.spl

```simple
struct CouplingMetrics:
    module_name: text
    cbo: i64              # Coupling Between Objects (= fan_out distinct deps)
    fan_in: i64           # Modules that depend on this module
    fan_out: i64          # Modules this module depends on
    instability: f64      # fan_out / (fan_in + fan_out), range [0, 1]
    abstractness: f64     # trait_count / total_type_count
    distance: f64         # |abstractness + instability - 1|

struct InstabilityInversion:
    stable_module: text
    unstable_module: text
    stable_instability: f64
    unstable_instability: f64
```

### layer_check.spl

```simple
struct LayerViolation:
    from_module: text     # Importing module (lower layer = violation source)
    to_module: text       # Imported module (higher layer = violation target)
    from_layer: i64       # Layer number of importing module
    to_layer: i64         # Layer number of imported module
```

### dsm.spl

```simple
struct DSMEntry:
    from_module: text
    to_module: text
    count: i64

struct DSMMatrix:
    modules: [text]       # Ordered list of module names
    matrix: [[i64]]       # N x N dependency counts
```

### lcom.spl

```simple
struct MethodFieldAccess:
    method_name: text
    fields_accessed: [text]
    methods_called: [text]

struct LCOMResult:
    class_name: text
    lcom4: i64            # Connected components count (1 = cohesive)
    method_count: i64
    field_count: i64
    component_sizes: [i64]

struct ClassInfo:
    class_name: text
    methods: [MethodFieldAccess]
    field_names: [text]
```

### api_quality.spl

```simple
struct MethodUsage:
    method_name: text
    external_call_count: i64

struct PublicAPIMetrics:
    module_name: text
    public_method_count: i64
    public_field_count: i64
    total_method_count: i64
    total_field_count: i64
    pss: i64              # Public Surface Size = pub methods + pub fields
    public_ratio: f64     # pss / total members
    avg_param_count: f64
    max_param_count: i64
    overload_groups: i64  # Overloaded method name groups
    eur: f64              # External Usage Ratio
    entropy: f64          # Normalized Shannon entropy over call counts
    api_complexity: f64   # Weighted composite index
```

### atss.spl

```simple
struct ATSSWarning:
    code: text
    severity: text
    message: text
    fn1_name: text
    fn2_name: text
    fn1_types: [text]
    fn2_types: [text]
    edit_distance: i64

    fn fmt() -> text      # Formats as "[code] severity: message"

struct TypeVector:
    fn_name: text
    types: [text]
    hash: i64
```

### relaxed_tokenizer.spl

```simple
struct RelaxedToken:
    kind_ordinal: i64
    line: i64
    column: i64

struct RelaxedMatch:
    file_a_line_start: i64
    file_a_line_end: i64
    file_b_line_start: i64
    file_b_line_end: i64
    matching_tokens: i64
    gap_lines: i64
```

### gap_matcher.spl

```simple
struct MatchBlock:
    start_line: i64
    end_line: i64
    is_gap: bool

struct GapMatch:
    blocks: [MatchBlock]
    total_matching_lines: i64
    total_gap_lines: i64

struct RawSegment:          # Internal
    a_start: i64
    a_end: i64
    b_start: i64
    b_end: i64
    token_count: i64
```

### report.spl

```simple
struct CouplingReport:
    metrics: [CouplingMetrics]
    cycles: [[text]]
    layer_violations: [LayerViolation]
    inversions: [InstabilityInversion]
    lcom_results: [LCOMResult]
    api_metrics: [PublicAPIMetrics]
    dsm: Option<DSMMatrix>
    atss_warnings: [ATSSWarning]
    cbo_threshold: i64
```

### main.spl

```simple
struct CouplingCLIConfig:
    format: text              # "text" | "json" | "md"
    cbo_threshold: i64        # Default: 15
    show_layers_only: bool
    show_dsm: bool
    show_cycles_only: bool
    show_api: bool
    show_lcom: bool
    relaxed: bool
    gap_tolerance: i64        # Default: 0
    atss_threshold: i64       # Default: 1
    target_path: text         # Default: "src/"
```

---

## 3. API Surface

### metrics.spl -- Graph metrics and cycle detection

| Function | Signature | Description |
|----------|-----------|-------------|
| `compute_fan_out` | `(graph: ImportGraph) -> Dict<text, i64>` | Out-degree per module |
| `compute_fan_in` | `(graph: ImportGraph) -> Dict<text, i64>` | In-degree per module |
| `compute_all_metrics` | `(graph: ImportGraph) -> [CouplingMetrics]` | CBO, fan-in/out, instability (abstractness=0) |
| `compute_all_metrics_with_abstractions` | `(graph: ImportGraph, trait_counts: Dict<text, i64>, type_counts: Dict<text, i64>) -> [CouplingMetrics]` | Full metrics including abstractness and distance |
| `find_instability_inversions` | `(metrics: [CouplingMetrics], graph: ImportGraph) -> [InstabilityInversion]` | Stable modules depending on unstable modules |
| `find_cycles` | `(graph: ImportGraph) -> [[text]]` | SCC cycle detection via graph library |

### layer_check.spl -- Layer ordering enforcement

| Function | Signature | Description |
|----------|-----------|-------------|
| `extract_layer_number` | `(module_path: text) -> Option<i64>` | Parse "NN.name" segments to layer number |
| `try_parse_layer_segment` | `(segment: text) -> Option<i64>` | Parse a single path segment |
| `is_digit` | `(ch: text) -> bool` | Character digit check |
| `find_layer_violations` | `(graph: ImportGraph) -> [LayerViolation]` | Find all backward layer dependencies |
| `format_violation` | `(v: LayerViolation) -> text` | Format a single violation for display |

### dsm.spl -- Dependency Structure Matrix

| Function | Signature | Description |
|----------|-----------|-------------|
| `build_dsm` | `(graph: ImportGraph) -> DSMMatrix` | Alphabetically sorted DSM |
| `build_layer_ordered_dsm` | `(graph: ImportGraph) -> DSMMatrix` | Layer-number sorted DSM |
| `build_dsm_with_order` | `(graph: ImportGraph, modules: [text]) -> DSMMatrix` | DSM with custom module ordering |
| `get_layer_for_sort` | `(module_path: text) -> i64` | Extract layer number for sorting |
| `format_dsm_text` | `(dsm: DSMMatrix) -> text` | Text table output |
| `format_dsm_markdown` | `(dsm: DSMMatrix) -> text` | Markdown table output |
| `format_dsm_json` | `(dsm: DSMMatrix) -> text` | JSON output |

### lcom.spl -- Cohesion metrics

| Function | Signature | Description |
|----------|-----------|-------------|
| `compute_lcom4` | `(class_name: text, methods: [MethodFieldAccess]) -> LCOMResult` | LCOM4 via union-find on method-field graph |
| `compute_all_lcom` | `(class_data: [ClassInfo]) -> [LCOMResult]` | Batch LCOM4 over multiple classes |
| `lcom_to_text` | `(result: LCOMResult) -> text` | Format single LCOM result |
| `lcom_report` | `(results: [LCOMResult]) -> text` | Format full LCOM report |
| `uf_init` | `(n: i64)` | Initialize union-find (module-level state) |
| `uf_find` | `(x: i64) -> i64` | Find with path compression |
| `uf_union` | `(a: i64, b: i64)` | Union by rank |

### api_quality.spl -- Public API quality metrics

| Function | Signature | Description |
|----------|-----------|-------------|
| `compute_pss` | `(pub_methods: i64, pub_fields: i64) -> i64` | Public Surface Size |
| `compute_public_ratio` | `(pss: i64, total: i64) -> f64` | PSS / total members |
| `compute_avg_param_count` | `(param_counts: [i64]) -> f64` | Average params per public method |
| `compute_max_param_count` | `(param_counts: [i64]) -> i64` | Maximum params on any public method |
| `compute_overload_groups` | `(method_names: [text]) -> i64` | Count of overloaded name groups |
| `compute_eur` | `(usages: [MethodUsage], total_public: i64) -> f64` | External Usage Ratio |
| `compute_entropy` | `(usages: [MethodUsage]) -> f64` | Normalized Shannon entropy |
| `compute_api_complexity` | `(metrics: PublicAPIMetrics) -> f64` | Weighted composite score |
| `compute_api_quality` | `(module_name: text, ...) -> PublicAPIMetrics` | Full API quality computation |
| `api_quality_to_text` | `(m: PublicAPIMetrics) -> text` | Format single module |
| `api_quality_report` | `(metrics_list: [PublicAPIMetrics]) -> text` | Format full report |

### atss.spl -- Argument Type Set Similarity

| Function | Signature | Description |
|----------|-----------|-------------|
| `collect_functions_for_atss` | `(decl_indices: [i64])` | Collect function defs from AST declaration tables |
| `extract_type_vectors` | `(fn_names: {text: [text]}, fn_types: {text: [text]}) -> [TypeVector]` | Build sorted type vectors per function |
| `compute_type_hash` | `(types: [text]) -> i64` | Hash a type vector for exact-match grouping |
| `type_set_edit_distance` | `(a: [text], b: [text]) -> i64` | Edit distance between type sets |
| `generate_deletion_variants` | `(types: [text]) -> [[text]]` | 1-deletion variants for near-match detection |
| `find_similar_signatures` | `(vectors: [TypeVector], threshold: i64) -> [ATSSWarning]` | Find pairs within edit distance threshold |
| `check_atss` | `(decl_indices: [i64], threshold: i64) -> [ATSSWarning]` | End-to-end ATSS check |

### relaxed_tokenizer.spl -- Token normalization

| Function | Signature | Description |
|----------|-----------|-------------|
| `token_kind_ordinal` | `(kind: SimpleTokenKind) -> i64` | Map token kind to integer ordinal |
| `to_relaxed_tokens` | `(tokens: [SimpleToken]) -> [RelaxedToken]` | Strip values, keep kind + position |
| `relaxed_rolling_hash` | `(tokens: [RelaxedToken], start: i64, window: i64) -> i64` | Rolling hash over token kind ordinals |
| `relaxed_power_mod` | `(base: i64, exp: i64, mod_val: i64) -> i64` | Modular exponentiation for hash |
| `find_relaxed_duplicates` | `(source_a: text, source_b: text, config: DuplicationConfig, min_tokens: i64) -> [RelaxedMatch]` | Cross-file structural duplicate detection |
| `merge_relaxed_matches` | `(matches: [RelaxedMatch]) -> [RelaxedMatch]` | Merge overlapping matches |
| `sort_relaxed_matches` | `(matches: [RelaxedMatch]) -> [RelaxedMatch]` | Sort by file_a_line_start |

### gap_matcher.spl -- Gap-tolerant matching

| Function | Signature | Description |
|----------|-----------|-------------|
| `find_raw_matches` | `(tokens_a: [RelaxedToken], tokens_b: [RelaxedToken], min_match: i64) -> [RawSegment]` | Find exact-match segments via rolling hash |
| `merge_with_gaps` | `(segments: [RawSegment], gap_tolerance: i64) -> [GapMatch]` | Merge adjacent segments allowing N gap lines |
| `build_gap_match` | `(segments: [RawSegment]) -> GapMatch` | Build GapMatch from a group of segments |
| `find_with_gap_tolerance` | `(tokens_a: [RelaxedToken], tokens_b: [RelaxedToken], min_match: i64, gap_tolerance: i64) -> [GapMatch]` | End-to-end gap-tolerant duplicate detection |

### report.spl -- Report formatting

| Function | Signature | Description |
|----------|-----------|-------------|
| `format_text` | `(report: CouplingReport) -> text` | Full text report with warnings |
| `format_json` | `(report: CouplingReport) -> text` | Structured JSON output |
| `format_markdown` | `(report: CouplingReport) -> text` | Markdown report |
| `format_dsm_text` | `(dsm: DSMMatrix) -> text` | DSM-only text table |
| `format_dsm_markdown` | `(dsm: DSMMatrix) -> text` | DSM-only markdown table |
| `format_layers_text` | `(violations: [LayerViolation]) -> text` | Layer violations only |
| `format_cycles_text` | `(cycles: [[text]]) -> text` | SCC cycles only |

### main.spl -- CLI orchestration

| Function | Signature | Description |
|----------|-----------|-------------|
| `default_cli_config` | `() -> CouplingCLIConfig` | Default config (threshold=15, format=text, etc.) |
| `parse_coupling_args` | `(args: [text]) -> CouplingCLIConfig` | Parse CLI flags |
| `run_coupling_analysis` | `(args: [text], graph: ImportGraph) -> i64` | Full analysis pipeline, returns exit code |

---

## 4. Integration Points

### Inputs from existing compiler infrastructure

| Dependency | Module | What it provides |
|------------|--------|------------------|
| `ImportGraph` | `compiler.common.dependency.graph` | Adjacency list of module-to-module import edges (`ImportGraph`, `ImportEdge`, `ImportKind`) |
| `SCC algorithm` | `std.graph.strongly_connected_components` | Tarjan's SCC via `graph_new`, `graph_add_vertex`, `graph_add_edge_unweighted`, `graph_strongly_connected_components` |
| `AST declarations` | `compiler.core.ast` | `DECL_FN`, `decl_tag`, `decl_name`, `decl_params`, `decl_param_types` for ATSS function extraction |
| `Existing tokenizer` | `compiler.tools.duplicate_check.tokenizer` | `SimpleToken`, `SimpleTokenKind`, `tokenize()` for relaxed tokenization |
| `Duplication config` | `compiler.tools.duplicate_check.config` | `DuplicationConfig` extended with `relaxed` and `gap_tolerance` fields |
| `Visibility system` | `compiler.common.dependency.visibility` | 4-level visibility hierarchy for PSS/EUR computation |
| `Math runtime` | `extern fn rt_math_log` | Natural logarithm for Shannon entropy computation |

### Outputs consumed by other subsystems

| Consumer | What it receives |
|----------|-----------------|
| CLI (`bin/simple build coupling`) | Formatted text/JSON/markdown report via `run_coupling_analysis` |
| Lint system (`bin/simple build lint`) | Lint rules W0501-W0510 registered in `src/compiler/35.semantics/lint/coupling.spl` |
| CI pipelines | JSON output for automated threshold checking |

### CLI flag dispatch

The `main.spl` orchestrator uses `CouplingCLIConfig` flags to selectively enable analysis passes:

- `--layers` -> `find_layer_violations()` only -> `format_layers_text()`
- `--cycles` -> `find_cycles()` only -> `format_cycles_text()`
- `--dsm` -> `build_layer_ordered_dsm()` -> `format_dsm_*`
- `--api` -> `compute_api_quality()` -> `api_quality_report()`
- `--lcom` -> `compute_all_lcom()` -> `lcom_report()`
- (default) -> all metrics + full `CouplingReport` -> `format_text/json/markdown()`

---

## 5. Data Flow

```
                         Source Files (.spl)
                               |
                               v
                    +-----------------------+
                    |   Compiler Pipeline   |
                    |  (parse -> resolve)   |
                    +-----------------------+
                         |            |
                         v            v
              +----------------+  +-------------------+
              |  ImportGraph   |  |  AST Declarations |
              | (adjacency     |  | (decl_tag,        |
              |  list of       |  |  decl_name,       |
              |  module deps)  |  |  decl_param_types)|
              +----------------+  +-------------------+
                   |    |    |           |         |
       +-----------+    |    +------+    |         |
       |                |           |    |         |
       v                v           v    v         v
+-------------+  +------------+  +--------+  +----------+
| metrics.spl |  | layer_     |  | dsm.spl|  | atss.spl |
| fan_in/out  |  | check.spl  |  | N x N  |  | type-set |
| CBO, I, A,  |  | extract    |  | matrix |  | edit dist|
| D, SCC      |  | violations |  |        |  |          |
+-------------+  +------------+  +--------+  +----------+
       |                |           |              |
       v                |           |              |
+------------------+    |           |              |
| find_instability |    |           |              |
| _inversions()    |    |           |              |
+------------------+    |           |              |
       |                |           |              |
       +-------+--------+-----------+--------------+
               |
               v
    +----------------------------+       +------------------+
    |  Class/Method Analysis     |       | relaxed_         |
    |  (from AST walk)           |       | tokenizer.spl    |
    +----------------------------+       | token-kind-only  |
         |              |               +------------------+
         v              v                       |
  +----------+   +--------------+               v
  | lcom.spl |   | api_quality  |        +-------------+
  | union-   |   | .spl         |        | gap_matcher  |
  | find on  |   | PSS, EUR,    |        | .spl         |
  | method-  |   | entropy,     |        | rolling hash |
  | field    |   | complexity   |        | + gap merge  |
  | graph    |   |              |        +-------------+
  +----------+   +--------------+               |
       |              |                         |
       +--------------+-------------------------+
                      |
                      v
            +-------------------+
            |   report.spl      |
            |   CouplingReport  |
            |   aggregate all   |
            |   results         |
            +-------------------+
                      |
          +-----------+-----------+
          |           |           |
          v           v           v
     format_text  format_json  format_markdown
          |           |           |
          v           v           v
            +-------------------+
            |    main.spl       |
            |    CLI dispatch   |
            |    stdout output  |
            +-------------------+
```

### Step-by-step flow

1. **Graph construction**: The compiler pipeline populates `ImportGraph` during module resolution. Each `use` statement adds an edge.
2. **Metric computation**: `compute_all_metrics()` or `compute_all_metrics_with_abstractions()` walks the `ImportGraph` to compute per-module fan-in, fan-out, CBO, instability, abstractness, and distance.
3. **Cycle detection**: `find_cycles()` converts the `ImportGraph` adjacency list to the `std.graph` format and calls `graph_strongly_connected_components()` (Tarjan's algorithm), filtering to components with >1 member.
4. **Layer enforcement**: `find_layer_violations()` extracts layer numbers from module paths (e.g., `"compiler/30.types/foo"` -> 30) and flags edges where source layer number is less than target layer number (backward dependency).
5. **DSM construction**: `build_layer_ordered_dsm()` creates an N x N matrix of dependency counts, sorted by layer number within each compiler layer group.
6. **LCOM4 computation**: For each class, `compute_lcom4()` builds an undirected graph where methods are nodes, edges connect methods sharing field access or calling each other, then counts connected components via union-find. LCOM4 = 1 means fully cohesive.
7. **API quality**: `compute_api_quality()` calculates PSS (public methods + fields), public ratio, EUR (externally-used / total public), Shannon entropy over call-site distribution, and a weighted composite complexity index.
8. **ATSS detection**: `check_atss()` extracts sorted type vectors from function declarations, hashes them for exact-match grouping, generates 1-deletion variants for near-match detection, and reports pairs within the edit distance threshold.
9. **Relaxed duplication**: `to_relaxed_tokens()` normalizes source to token-kind ordinals only (discarding identifiers and literal values). `find_with_gap_tolerance()` uses rolling hash to find matching subsequences, then merges adjacent segments allowing N gap lines.
10. **Report assembly**: All results are collected into a `CouplingReport` struct. The formatter selected by `--format` renders the final output.

---

## 6. Cross-References

| Document | Path | Relationship |
|----------|------|-------------|
| Requirement | `doc/requirement/coupling_analysis.md` | Acceptance criteria AC-01 through AC-24; scope definition |
| Research | `doc/research/coupling_analysis.md` | Literature survey, metric definitions, algorithm choices |
| Plan | `doc/plan/coupling_analysis.md` | 17 tasks in 5 groups, dependency DAG, file plan, model assignment |
| Design (this doc) | `doc/design/coupling_analysis.md` | Module structure, types, API, data flow |
| System Tests | `test/system/coupling_analysis_spec.spl` | End-to-end verification of all metrics and CLI output |
| ImportGraph | `src/compiler/00.common/dependency/graph.spl` | Primary input: module dependency adjacency list |
| SCC algorithm | `src/lib/common/graph/strongly_connected.spl` | Tarjan's SCC implementation used by `find_cycles()` |
| Call graph | `src/compiler/10.frontend/core/call_graph.spl` | Used for RFC metric computation |
| Visibility | `src/compiler/00.common/dependency/visibility.spl` | 4-level hierarchy for PSS/EUR |
| Lint infra | `src/compiler/35.semantics/lint/__init__.spl` | Registration point for W0501-W0510 |
| Coupling lint rules | `src/compiler/35.semantics/lint/coupling.spl` | Lint rule implementations |
| Dup typed args | `src/compiler/35.semantics/lint/duplicate_typed_args.spl` | Extended for ATSS cross-function comparison |
| Existing tokenizer | `src/app/duplicate_check/tokenizer.spl` | Wrapped by `relaxed_tokenizer.spl` |
| Dup config | `src/app/duplicate_check/config.spl` | Extended with `relaxed` and `gap_tolerance` fields |
| DepGraph tool | `src/compiler/90.tools/depgraph/` | Existing dependency graph tooling (coupling extends this) |
| Architecture | `doc/architecture/dependency_graphs.md` | Architectural context for dependency analysis |
