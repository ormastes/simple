# Performance Analysis and Collection Refactoring — System Scenario Manual

- **Executable Spec:** `test/03_system/app/compiler/feature/perf_analysis_collection_refactoring_spec.spl`
- **Overhead Guard Spec:** `test/05_perf/compiler/perf_analyzer_overhead_guard_spec.spl`
- **Canonical Design & Plan:** `doc/03_plan/compiler/performance_analysis_and_collection_refactoring_2026-11-18.md`
- **Shared V1 Contracts:** `src/compiler/35.semantics/perf/perf_analysis_contracts_v1.spl`
- **Status:** Implementing (Wave F)

---

## Purpose

This manual walks through the primary system scenarios for Simple's symbolic performance analyzer and safe collection-refactoring pipeline without requiring the reader to open the executable `.spl` spec source.

The pipeline enforces four core invariants:

1. **Style-independent symbolic cost propagation (`D01`–`D04`):** Imperative `for`/`while` loops, iterators, callbacks, and functional collection pipelines are analyzed uniformly with explicit multivariate input sizes (`n = length(keys)`, `m = length(records)`).
2. **Separation of recognition, 13-point semantic legality, and profitability (`D06`, `D10`):** Recognizing a loop shape (`PERF-STYLE-001`) never implies that rewriting it is legal or faster; automatic `--fix-safe` edits require discharging all 13 `SafetyObligationKind` preconditions and matching revision/dependency stamps in `EditTransaction`.
3. **Three-valued resource contract verification (`Verified | Refuted | Unproved`):** Loose upper bounds and incomplete coverage report `Unproved` (`PERF-CONTRACT-002`), never a false `Refuted` (`PERF-CONTRACT-001`) claim.
4. **Feature-off bootstrap and normal-compile isolation (`D11`, `D12`, `I10`):** Normal compilation (`T0`) neither allocates `perf_analysis_contracts_v1` side tables nor injects runtime counters.

---

## Scenario 1: Interprocedural Caller Propagation (`count_matches` inside `count_for_all` -> `PERF-COST-001`)

### Input Program Shape

```simple
fn count_matches(records, key):
    var count = 0
    for record in records:
        if record.key == key:
            count = count + 1
    count

fn count_for_all(keys, records):
    var result = []
    for key in keys:
        result.push(count_matches(records, key))
    result
```

### Step-by-Step Pipeline Execution

1. **One-pass HIR fact collection (`collect_hir_perf_facts`):**
   - Scans `count_matches` and `count_for_all` once against the verified `CollectionOperationRegistry` (`stdlib-cost-v1`), recording `functions_scanned = 2`, `loop_depth = 1` on both loop-body operations, and `coverage_complete = true`.
   - Separately verifies `resolve_builtin_collection_operation` (`builtin_collection.spl`): `Array.map` and capture-free `Array.filter` single-parameter lambdas receive `BuiltinCollection` identity, whereas user-defined `append` lookalikes (`S13`) and unmodeled callback shapes fail closed (`None`).
2. **Caller summary substitution (`FunctionCostSummaryV1`):**
   - Preserves independent size parameters `n = length(keys)` and `m = length(records)` (`C03`, `C07`) rather than collapsing both into a single `n`.
   - Substitutes `KnownCalleeCost("count_matches", m)` inside the `n`-iteration caller traversal, yielding `BoundEvidenceV1` with `rendered_expression = "n*m"`, `relation = Exact` (for modeled key comparisons on normal completion), and `regime = WorstCase`.
3. **Actionable caller diagnostic (`PERF-COST-001`) and `ReviewRequired` redesign (`PERF-ALG-001`):**
   - Emits `PERF-COST-001` at `count_for_all` with a two-node `ProvenanceEdgeV1` cause chain (`outer_traversal` -> `callee_linear_scan`).
   - Attaches a `ReviewRequired` `AlgorithmChange` candidate (`PERF-ALG-001`: build key counts once via `count_by`) that explicitly discloses expected work `O(m+n)` versus auxiliary memory `O(distinct_keys)` under key hash/equality assumptions, and notes that grouped joins retain `O(n+m+k)` output match work (`C12`, `S16`).

---

## Scenario 2: Verified Local `FilterMap` Refactor (`PERF-STYLE-001`) vs Blocked Aliasing (`PERF-FIX-001`)

### Candidate Shape

```simple
# Original eager imperative builder loop:
var result = []
for item in items:
    if valid(item):
        result.push(transform(item))

# VerifiedSafe replacement (when all 13 obligations pass):
val result = items.iter()
    .filter(valid)
    .map(transform)
    .collect()
```

### Verification Outcomes

| Case | 13-Point Obligations | `PerfFixApplicability` | `EditTransaction` Outcome |
|------|----------------------|------------------------|---------------------------|
| Fresh local builder, distinct `items`, compatible callback effects, current revision `v7` (`S01`, `S02`, `S14`) | All 13 `discharged = true` | `VerifiedSafe` (`PERF-STYLE-001` Hint) | `ApplyStatus.Applied` — terminal `.collect()` preserved; note states traversal cost is unchanged and runtime improvement is not established. |
| `items` may alias `result` or external alias observes builder identity (`S03`, `S06`) | `aliasing` / `collection_identity` `discharged = false` | `Unavailable` (`PERF-FIX-001`, `isPreferred = false`) | `ApplyStatus.DisabledCandidate` — original valid loop text remains untouched and unwarned. |
| Editor buffer advanced to `v8` after discovery (`I01`) | Stale document version | Rejected at apply | `ApplyStatus.StaleVersion` — zero bytes modified. |
| Callee effect/summary digest changed without editing caller text (`I02`) | Stale `source_hash` / `dependency_fingerprint` | Rejected at apply | `ApplyStatus.StaleHash` — zero bytes modified. |
| Batch contains overlapping replacement spans (`I07`) | Conflicting byte ranges | Rejected atomically | `ApplyStatus.OverlappingEdits` — zero partial edits applied. |

---

## Scenario 3: Three-Valued Resource Contracts (`Verified | Refuted | Unproved`) and Baseline Diffs

1. **`Verified`:** Inferred `O(n)` `UpperBound` satisfies a declared `@cost(work <= linear(size(items)))` contract.
2. **`Refuted` (`PERF-CONTRACT-001`):** Tight or exact `n*n` bound refutes a declared linear contract in its enforcement profile.
3. **`Unproved` (`PERF-CONTRACT-002`, `C15`):** A monotone two-pointer loop whose `T1` summary only establishes a loose `O(n^2)` `UpperBound` produces `ContractVerificationVerdict.Unproved` with `"unproved"` wording — **never** `Refuted`, because a linear function mathematically satisfies an `O(n^2)` upper bound.
4. **Baseline model-migration separation (`C16`, `PERF-COST-002`):** Comparing baseline and current summaries classifies an `stdlib-cost-v1 -> stdlib-cost-v2` upgrade on unchanged `semantic_revision` as `model_related`, while an `O(n) -> O(n*n)` increase under the same model version on a new source revision emits `source_related:PERF-COST-002`.

---

## Scenario 4: Behavioral Trace Equivalence (`S01`, `S02`, `S07`, `S08`, `S12`)

- **Interleaved `FilterMap` callback order (`S01`, `S02`):** On `[1, 2, 3, 4]`, both the imperative loop and fused `iter().filter(valid).map(transform).collect()` produce `[20, 40]` and the exact event sequence `["pred:1", "pred:2", "map:2", "pred:3", "pred:4", "map:4"]`.
- **Short-circuit search consumption (`S12`):** Searching `[3, 4, 5, 6]` for the first even item stops at `4` with `consumed = 2` (`["check:3", "check:4"]`), never evaluating items `5` or `6`.
- **Empty-input non-identity fold seed (`S07`):** Folding `[]` with seed `100` returns `100` with zero step calls, matching `var acc = 100; for item in []: ...`.
- **Sequential ordered `fold` vs invalid reassociation (`S08`):** Left-to-right subtraction `fold(100, [10, 20, 5], -)` evaluates `(((100 - 10) - 20) - 5) = 65`, matching the imperative loop, whereas right-associated `(100 - (10 - (20 - 5))) = 105` diverges — demonstrating why accumulator loops map to sequential ordered `fold` rather than parallel reduction unless associativity and numeric permissions are proven.
