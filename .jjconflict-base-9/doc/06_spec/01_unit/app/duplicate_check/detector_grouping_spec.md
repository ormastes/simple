# Detector Grouping Specification

> 1. ensure clean dir

<!-- sdn-diagram:id=detector_grouping_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=detector_grouping_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

detector_grouping_spec -> compiler
detector_grouping_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=detector_grouping_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Detector Grouping Specification

## Scenarios

### duplicate_check detector grouping regressions

#### keeps exact-match occurrences across three files

1. ensure clean dir
2. write test file
3. write test file
4. write test file
   - Expected: groups[0].occurrences equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_duplicate_detector_exact"
ensure_clean_dir(root)

val body = "fn shared_logic(seed: i64) -> i64:\n    val base = seed + 1\n    val total = base * 2\n    return total\n"
val file_a = "{root}/a.spl"
val file_b = "{root}/b.spl"
val file_c = "{root}/c.spl"
write_test_file(file_a, body)
write_test_file(file_b, body)
write_test_file(file_c, body)

val groups = find_duplicates([file_a, file_b, file_c], cosine_config(), new_token_cache_manager())

expect(groups.len()).to_be_greater_than(0)
expect(groups[0].occurrences).to_equal(3)
```

</details>

#### keeps cosine groups across similar files

1. ensure clean dir
2. write test file
3. write test file
   - Expected: groups[0].occurrences equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_duplicate_detector_cosine"
ensure_clean_dir(root)

val file_a = "{root}/alpha.spl"
val file_b = "{root}/beta.spl"
val content_a = "fn alpha_logic(seed: i64) -> i64:\n    val alpha_base = seed + 1\n    val alpha_total = alpha_base * 2\n    if alpha_total > seed:\n        return alpha_total\n    return seed\n"
val content_b = "fn beta_logic(seed: i64) -> i64:\n    val beta_base = seed + 2\n    val beta_total = beta_base * 2\n    if beta_total > seed:\n        return beta_total\n    return seed\n"
write_test_file(file_a, content_a)
write_test_file(file_b, content_b)

val groups = find_duplicates([file_a, file_b], cosine_config(), new_token_cache_manager())

expect(groups.len()).to_be_greater_than(0)
expect(groups[0].occurrences).to_equal(2)
```

</details>

#### applies wildcard excludes during directory collection

1. ensure clean dir
2. write test file
   - Expected: rt_dir_create("{root}/doc", true) is true
3. write test file
4. write test file
5. var config = lexical config
   - Expected: contains_path(files, keep) is true
   - Expected: contains_path(files, spec) is false
   - Expected: contains_path(files, nested) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_duplicate_detector_collect"
ensure_clean_dir(root)

val keep = "{root}/keep_module.spl"
val spec = "{root}/skip_module_spec.spl"
val nested = "{root}/doc/skip_doc.spl"
write_test_file(keep, "fn keep():\n    1\n")
expect(rt_dir_create("{root}/doc", true)).to_equal(true)
write_test_file(spec, "fn skip_spec():\n    2\n")
write_test_file(nested, "fn skip_doc():\n    3\n")

var config = lexical_config()
config.exclude_patterns = ["**/*_spec.spl", "doc/"]

val files = collect_files(root, config)

expect(contains_path(files, keep)).to_equal(true)
expect(contains_path(files, spec)).to_equal(false)
expect(contains_path(files, nested)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/duplicate_check/detector_grouping_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- duplicate_check detector grouping regressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
