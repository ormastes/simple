# Phase1 Integration Specification

> 1. ensure clean dir

<!-- sdn-diagram:id=phase1_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=phase1_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

phase1_integration_spec -> compiler
phase1_integration_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=phase1_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Phase1 Integration Specification

## Scenarios

### Phase1 Integration

#### reuses the token cache across repeated scans

1. ensure clean dir
2. create test file
3. create test file
   - Expected: second_groups.len() equals `first_groups.len()`
   - Expected: second_stats equals `first_stats`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ensure_clean_dir(TEST_DIR)

val file_a = "{TEST_DIR}/cache_a.spl"
val file_b = "{TEST_DIR}/cache_b.spl"
val body = shared_logic_body("shared_cache", "cache", 1)
create_test_file(file_a, body)
create_test_file(file_b, body)

val config = phase1_test_config()
val cache_manager = new_token_cache_manager()

val first_groups = find_duplicates([file_a, file_b], config, cache_manager)
val first_stats = get_cache_stats(cache_manager)
val second_groups = find_duplicates([file_a, file_b], config, cache_manager)
val second_stats = get_cache_stats(cache_manager)

expect(first_groups.len()).to_be_greater_than(0)
expect(second_groups.len()).to_equal(first_groups.len())
expect(first_stats).to_contain("2 files")
expect(second_stats).to_equal(first_stats)
```

</details>

#### detects renamed logic when identifier normalization is enabled

1. ensure clean dir
2. create test file
3. create test file
   - Expected: groups[0].occurrences equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ensure_clean_dir(TEST_DIR)

val file_a = "{TEST_DIR}/normalize_a.spl"
val file_b = "{TEST_DIR}/normalize_b.spl"
create_test_file(file_a, shared_logic_body("alpha_logic", "alpha", 5))
create_test_file(file_b, shared_logic_body("beta_logic", "beta", 5))

val config = phase1_test_config()
config.ignore_identifiers = true
config.ignore_literals = false

val groups = find_duplicates([file_a, file_b], config, new_token_cache_manager())

expect(groups.len()).to_be_greater_than(0)
expect(groups[0].occurrences).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/duplicate_check/phase1_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Phase1 Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
