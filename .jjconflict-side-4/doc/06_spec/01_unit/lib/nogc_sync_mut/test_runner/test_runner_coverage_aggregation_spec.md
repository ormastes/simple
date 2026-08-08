# Cross-Process Coverage Aggregation Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 4 | 4 | 0 | 0 |

## Purpose

Proves that a strict compiler decision manifest can seed zero-count decisions
before child outcomes merge, that runtime rows cannot masquerade as a compiler
manifest, that separate child outcomes are retained, and that an aggregate
percentage cannot hide a file below its declared `# @cover` threshold.

## Scenarios

### pre-registers an untouched compiler decision before runtime outcomes merge

1. Record a compiler manifest containing one zero/zero decision row.
2. Require the untouched decision to appear as 0% covered.
3. Merge true and false runtime rows for the same stable key.
4. Require one covered decision at 100%, without duplicating the denominator.

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_coverage_state()
expect(record_compiler_decision_manifest_sdn(compiler_decision_manifest_sdn())).to_be(true)

val untouched = collect_coverage()
expect(untouched.total_decisions).to_equal(1)
expect(untouched.total_decisions_covered).to_equal(0)
expect(untouched.decision_pct).to_equal(0)

record_coverage_sdn(child_decision_sdn(1, 0))
record_coverage_sdn(child_decision_sdn(0, 1))
val exercised = collect_coverage()
expect(exercised.total_decisions).to_equal(1)
expect(exercised.total_decisions_covered).to_equal(1)
expect(exercised.decision_pct).to_equal(100)
reset_coverage_state()
```

</details>

### rejects runtime counts, event rows, and malformed compiler locations

The strict manifest boundary rejects a table row with a positive count and an
event-format runtime row, plus non-decimal and overflowing source locations.
Rejected input leaves the denominator empty; a valid zero-count manifest still
pre-registers its decision afterward.

This is runner-side TODO594 groundwork only. The compiler does not yet emit the
manifest, so these scenarios do not claim full source coverage or close
TODO594.

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_coverage_state()
expect(record_compiler_decision_manifest_sdn(compiler_decision_manifest_sdn(1, 1))).to_be(false)
expect(record_compiler_decision_manifest_sdn("decision src/owned/frame.spl:10 branch-1 true")).to_be(false)
val malformed = compiler_decision_manifest_sdn().replace(", 10, 4,", ", nope, 4,")
expect(record_compiler_decision_manifest_sdn(malformed)).to_be(false)
val overflow = compiler_decision_manifest_sdn().replace(", 10, 4,", ", 99999999999999999999, 4,")
expect(record_compiler_decision_manifest_sdn(overflow)).to_be(false)
expect(record_compiler_decision_manifest_sdn(compiler_decision_manifest_sdn())).to_be(true)
val coverage = collect_coverage()
expect(coverage.total_decisions).to_equal(1)
expect(coverage.total_decisions_covered).to_equal(0)
reset_coverage_state()
```

</details>

### merges true and false outcomes retained by separate child runs

1. Reset the parent coverage collector.
2. Record one child SDN with the true outcome.
3. Record another child SDN with the false outcome.
4. Collect the merged coverage report.
5. Require one file, one decision, and 100% decision coverage.

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_coverage_state()
record_coverage_sdn(child_decision_sdn(1, 0))
record_coverage_sdn(child_decision_sdn(0, 1))

val coverage = collect_coverage()
expect(coverage.files.len()).to_equal(1)
expect(coverage.files[0].path).to_equal("src/owned/frame.spl")
expect(coverage.files[0].decisions_total).to_equal(1)
expect(coverage.files[0].decisions_covered).to_equal(1)
expect(coverage.files[0].decision_pct).to_equal(100)
expect(coverage.total_decisions).to_equal(1)
expect(coverage.total_decisions_covered).to_equal(1)
expect(coverage.decision_pct).to_equal(100)
reset_coverage_state()
```

</details>

### rejects an owner below its annotated threshold despite 99 percent aggregate coverage

1. Record 100 decisions: 99 covered overall, but only one of two covered for
   `src/owned/frame.spl`.
2. Require the owner's `50%` annotation to pass and its `100%` annotation to
   fail.
3. Require missing targets and malformed percentages, including numeric-prefix
   forms such as `50junk%` and `50%%`, to fail closed.

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_coverage_state()
var sdn = "decisions |id, file, line, column, true_count, false_count|\n"
var i = 0
while i < 100:
    val path = if i < 2: "src/owned/frame.spl" else: "src/other/frame.spl"
    val false_count = if i == 0: 0 else: 1
    sdn = sdn + "    branch-{i}, {path}, {i + 1}, 4, 1, {false_count}\n"
    i = i + 1
sdn = sdn + "conditions |decision_id, condition_id, file, line, column, true_count, false_count|"
record_coverage_sdn(sdn)

val coverage = collect_coverage()
expect(coverage.decision_pct).to_equal(99)
expect(check_cover_annotation_threshold(coverage, "src/owned/frame.spl 50%")).to_be(true)
expect(check_cover_annotation_threshold(coverage, "src/owned/frame.spl 100%")).to_be(false)
expect(check_cover_annotation_threshold(coverage, "src/missing/frame.spl 100%")).to_be(false)
expect(check_cover_annotation_threshold(coverage, "src/owned/frame.spl nope")).to_be(false)
expect(check_cover_annotation_threshold(coverage, "src/owned/frame.spl 50junk%")).to_be(false)
expect(check_cover_annotation_threshold(coverage, "src/owned/frame.spl 50%%")).to_be(false)
reset_coverage_state()
```

</details>

## Evidence Status

The scenario contains real assertions and no placeholder pass. Its diagnostic
run timed out before a result on the available unaccepted runtime, so this
manual records source-ready coverage infrastructure rather than a PASS or a
measured whole-feature coverage percentage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Unit / test runner |
| Status | Active; runtime execution blocked |
| Source | `test/01_unit/lib/nogc_sync_mut/test_runner/test_runner_coverage_aggregation_spec.spl` |
| Updated | 2026-07-27 |
| Manual | Maintained after bounded docgen timeout |
