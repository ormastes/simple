# Launch Metadata Section Overlap Index Contract Specification

> Tests covering:

## Scenarios

### Launch metadata section-index operation contract [importance=critical; importance_weight=3]

### LM-P01: one indexed validation pass [importance=critical; importance_weight=3]

#### should return value-owned counters for decoded rows, indexed spans, sorting, and adjacent checks [importance=critical; importance_weight=3]

- Read the owning launch-metadata section-validation region


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the owning launch-metadata section-validation region")
val source = file_read_text("src/app/startup/launch_metadata.spl")
val region = source_region(source)
expect(region).to_contain("_LaunchMetadataSectionValidationCountersV1")
expect(region).to_contain("section_rows_decoded")
expect(region).to_contain("positive_spans_indexed")
expect(region).to_contain("sort_input_spans")
expect(region).to_contain("adjacent_span_checks")
expect(region).to_contain("_retained_smf_section_validation_v1")
```

</details>

<details>
<summary>Advanced: should replace the quadratic pairwise overlap loop with sorted adjacent spans [importance=critical; importance_weight=3]</summary>

#### should replace the quadratic pairwise overlap loop with sorted adjacent spans [importance=critical; importance_weight=3]

- Inspect the private validation source region for the sorted-span sweep
   - Expected: has_sort is true
   - Expected: region does not contain `section_starts`
   - Expected: region does not contain `section_ends`
   - Expected: region does not contain `while previous < section_starts.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the private validation source region for the sorted-span sweep")
val region = source_region(file_read_text("src/app/startup/launch_metadata.spl"))
val has_sort = region.contains("spans.sort()") or
    region.contains("array_sort_by(spans")
expect(has_sort).to_equal(true)
expect(region).to_contain("adjacent_span_checks = adjacent_span_checks + 1")
expect(region.contains("section_starts")).to_equal(false)
expect(region.contains("section_ends")).to_equal(false)
expect(region.contains("while previous < section_starts.len()")).to_equal(false)
```

</details>


</details>

#### should enforce the adjacent-check bound without counting sort comparisons [importance=critical; importance_weight=3]

- Inspect the operation-bound wording and counter increments
   - Expected: has_adjacent_guard is true
   - Expected: has_previous_end_check is true
   - Expected: has_counter_increment is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the operation-bound wording and counter increments")
val region = source_region(file_read_text("src/app/startup/launch_metadata.spl"))
val has_adjacent_guard = region.contains("spans.len()") and
    region.contains("while")
val has_previous_end_check = region.contains("previous.end")
val has_counter_increment = region.contains("adjacent_span_checks")
expect(has_adjacent_guard).to_equal(true)
expect(has_previous_end_check).to_equal(true)
expect(has_counter_increment).to_equal(true)
```

</details>

### LM-P02: deterministic wide-table evidence [importance=high; importance_weight=2]

#### should retain executable wide-table fixtures at 64 and 256 rows [importance=high; importance_weight=2]

- Read the behavior oracle and verify the first wide-table cardinalities


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the behavior oracle and verify the first wide-table cardinalities")
val behavior = file_read_text(
    "test/01_unit/app/startup/launch_metadata_section_index_spec.spl")
expect(behavior).to_contain("wide_valid_fixture(64)")
expect(behavior).to_contain("wide_valid_fixture(256)")
```

</details>

#### should retain executable wide-table fixtures at 1024 and 4096 rows [importance=high; importance_weight=2]

- Verify the larger cardinalities are real fixture calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify the larger cardinalities are real fixture calls")
val behavior = file_read_text(
    "test/01_unit/app/startup/launch_metadata_section_index_spec.spl")
expect(behavior).to_contain("wide_valid_fixture(1024)")
expect(behavior).to_contain("wide_valid_fixture(4096)")
expect(behavior).to_contain("launch_metadata_absent")
```

</details>

#### should compare the retained metadata through a byte-exact oracle rather than a timing claim [importance=high; importance_weight=2]

- Inspect the behavior oracle's exact serialized payload assertion
   - Expected: behavior).to_contain("render_launch_metadata_sidecar(result.metadata) equals `"`
   - Expected: behavior does not contain `time_now`
   - Expected: behavior does not contain `sleep(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the behavior oracle's exact serialized payload assertion")
val behavior = file_read_text(
    "test/01_unit/app/startup/launch_metadata_section_index_spec.spl")
expect(behavior).to_contain("render_launch_metadata_sidecar(result.metadata)).to_equal(")
expect(behavior).to_contain("launch_metadata_section_overlap")
expect(behavior).to_contain("launch_metadata_section_duplicate")
expect(behavior.contains("time_now")).to_equal(false)
expect(behavior.contains("sleep(")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/startup/launch_metadata_section_overlap_index_contract_spec.spl` |
| Updated | 2026-09-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Launch metadata section-index operation contract [importance=critical; importance_weight=3]
- LM-P01: one indexed validation pass [importance=critical; importance_weight=3]
- LM-P02: deterministic wide-table evidence [importance=high; importance_weight=2]

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


<!-- sdn-diagram:id=launch_metadata_section_overlap_index_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=launch_metadata_section_overlap_index_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

launch_metadata_section_overlap_index_contract_spec -> std
launch_metadata_section_overlap_index_contract_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=launch_metadata_section_overlap_index_contract_spec.arch hash=sha256:auto
+-----+      +-----------------------------------------------------+
| app | ---> | launch_metadata_section_overlap_index_contract_spec |
+-----+      +-----------------------------------------------------+
             +-----------------------------------------------------+
             | std                                                 |
             +-----------------------------------------------------+
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |
