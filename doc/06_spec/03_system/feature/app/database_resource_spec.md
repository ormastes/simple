# MCP Database Resource

> Tests the MCP database resource interface for querying bug, test, and feature databases through MCP tools. Verifies that database resources are correctly exposed, queryable, and return well-formed results via the MCP protocol.

<!-- sdn-diagram:id=database_resource_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_resource_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_resource_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_resource_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Database Resource

Tests the MCP database resource interface for querying bug, test, and feature databases through MCP tools. Verifies that database resources are correctly exposed, queryable, and return well-formed results via the MCP protocol.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/database_resource_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP database resource interface for querying bug, test, and feature
databases through MCP tools. Verifies that database resources are correctly
exposed, queryable, and return well-formed results via the MCP protocol.

## Scenarios

### Bug Database MCP Resource

#### read operations

#### returns JSON error for missing database

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = get_all_bugs(TEST_BUG_DB)
expect(json).to_contain("\"error\"")
expect(json).to_contain("Database not found")
```

</details>

#### returns stats error for missing database

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = get_bug_stats(TEST_BUG_DB)
expect(json).to_contain("\"error\"")
expect(json).to_contain("Database not found")
```

</details>

#### returns error for non-existent bug

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = get_bug_by_id(TEST_BUG_DB, "nonexistent")
expect(json).to_contain("\"error\"")
expect(json).to_contain("not found")
```

</details>

#### write operations

#### adds bug via JSON

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bug_json = "{\"id\": \"test_001\", \"severity\": \"P2\", \"status\": \"Open\", \"title\": \"Test bug\", \"file\": \"test.spl\", \"line\": 42, \"reproducible_by\": \"test_spec\"}"
val result = add_bug_from_json(TEST_BUG_DB, bug_json)
expect(result).to_contain("\"success\":true")
expect(result).to_contain("\"id\":\"test_001\"")
```

</details>

#### retrieves added bug

1. add bug from json


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bug_json = "{\"id\": \"test_002\", \"severity\": \"P1\", \"status\": \"Open\", \"title\": \"Critical bug\", \"file\": \"critical.spl\", \"line\": 100, \"reproducible_by\": \"critical_spec\"}"
add_bug_from_json(TEST_BUG_DB, bug_json)
val json = get_bug_by_id(TEST_BUG_DB, "test_002")
expect(json).to_contain("\"id\":\"test_002\"")
```

</details>

#### updates bug status

1. add bug from json


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bug_json = "{\"id\": \"test_003\", \"severity\": \"P2\", \"status\": \"Open\", \"title\": \"Bug to fix\", \"file\": \"fix.spl\", \"line\": 50, \"reproducible_by\": \"fix_spec\"}"
add_bug_from_json(TEST_BUG_DB, bug_json)
val update_json = "{\"status\": \"Fixed\"}"
val result = update_bug_from_json(TEST_BUG_DB, "test_003", update_json)
expect(result).to_contain("\"success\":true")
```

</details>

#### fails to add bug without id

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_json = "{\"title\": \"No ID bug\"}"
val result = add_bug_from_json(TEST_BUG_DB, bad_json)
expect(result).to_contain("\"error\"")
```

</details>

#### query operations

#### gets open bugs only

1. add bug from json

2. add bug from json
   - Expected: json does not contain `"id":"fixed_001"`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
add_bug_from_json(TEST_BUG_DB, "{\"id\": \"open_001\", \"severity\": \"P2\", \"status\": \"Open\", \"title\": \"Open bug\"}")
add_bug_from_json(TEST_BUG_DB, "{\"id\": \"fixed_001\", \"severity\": \"P2\", \"status\": \"Fixed\", \"title\": \"Fixed bug\"}")
val json = get_open_bugs(TEST_BUG_DB)
expect(json).to_contain("\"total\":1")
expect(json).to_contain("\"id\":\"open_001\"")
expect(json.contains("\"id\":\"fixed_001\"")).to_equal(false)
```

</details>

#### gets critical bugs only

1. add bug from json

2. add bug from json
   - Expected: json does not contain `"id":"normal_001"`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
add_bug_from_json(TEST_BUG_DB, "{\"id\": \"critical_001\", \"severity\": \"P1\", \"status\": \"Open\", \"title\": \"Critical bug\"}")
add_bug_from_json(TEST_BUG_DB, "{\"id\": \"normal_001\", \"severity\": \"P3\", \"status\": \"Open\", \"title\": \"Normal bug\"}")
val json = get_critical_bugs(TEST_BUG_DB)
expect(json).to_contain("\"total\":1")
expect(json).to_contain("\"id\":\"critical_001\"")
expect(json.contains("\"id\":\"normal_001\"")).to_equal(false)
```

</details>

#### calculates correct stats

1. add bug from json

2. add bug from json


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
add_bug_from_json(TEST_BUG_DB, "{\"id\": \"stats_001\", \"severity\": \"P0\", \"status\": \"Open\", \"title\": \"Release blocker\"}")
add_bug_from_json(TEST_BUG_DB, "{\"id\": \"stats_002\", \"severity\": \"P2\", \"status\": \"Fixed\", \"title\": \"Fixed bug\"}")
val json = get_bug_stats(TEST_BUG_DB)
expect(json).to_contain("\"total\":2")
expect(json).to_contain("\"open\":1")
expect(json).to_contain("\"fixed\":1")
expect(json).to_contain("\"p0\":1")
```

</details>

### Feature Database MCP Resource

#### read operations

#### returns empty list for new database

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = get_all_features(TEST_FEATURE_DB)
expect(json).to_contain("\"total\":0")
expect(json).to_contain("\"features\":[]")
```

</details>

#### returns stats for empty database

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = get_feature_stats(TEST_FEATURE_DB)
expect(json).to_contain("\"total\":0")
expect(json).to_contain("\"done\":0")
expect(json).to_contain("\"planned\":0")
```

</details>

#### write operations

#### adds feature via JSON

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feature_json = "{\"id\": \"feat_001\", \"category\": \"compiler\", \"name\": \"Parser feature\", \"description\": \"Parse expressions\", \"spec_file\": \"parser_spec.spl\", \"pure_status\": \"Planned\", \"hybrid_status\": \"Planned\", \"llvm_status\": \"Planned\"}"
val result = add_feature_from_json(TEST_FEATURE_DB, feature_json)
expect(result).to_contain("\"success\":true")
expect(result).to_contain("\"id\":\"feat_001\"")
```

</details>

#### retrieves added feature

1. add feature from json


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feature_json = "{\"id\": \"feat_002\", \"category\": \"runtime\", \"name\": \"Runtime feature\", \"description\": \"Run code\", \"spec_file\": \"runtime_spec.spl\", \"pure_status\": \"Planned\", \"hybrid_status\": \"Planned\", \"llvm_status\": \"Planned\"}"
add_feature_from_json(TEST_FEATURE_DB, feature_json)
val json = get_feature_by_id(TEST_FEATURE_DB, "feat_002")
expect(json).to_contain("\"id\":\"feat_002\"")
expect(json).to_contain("\"category\":\"runtime\"")
expect(json).to_contain("\"pure_status\":\"planned\"")
```

</details>

#### updates feature status

1. add feature from json


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feature_json = "{\"id\": \"feat_003\", \"category\": \"compiler\", \"name\": \"Status feature\", \"description\": \"Update status\", \"spec_file\": \"status_spec.spl\", \"pure_status\": \"Planned\", \"hybrid_status\": \"Planned\", \"llvm_status\": \"Planned\"}"
add_feature_from_json(TEST_FEATURE_DB, feature_json)
val result = update_feature_from_json(TEST_FEATURE_DB, "feat_003", "{\"name\": \"Updated status feature\"}")
expect(result).to_contain("\"success\":true")
val json = get_feature_by_id(TEST_FEATURE_DB, "feat_003")
expect(json).to_contain("\"name\":\"Updated status feature\"")
expect(json).to_contain("\"pure_status\":\"planned\"")
```

</details>

#### query operations

#### gets features by category

1. add feature from json

2. add feature from json
   - Expected: json does not contain `"id":"feat_005"`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
add_feature_from_json(TEST_FEATURE_DB, "{\"id\": \"feat_004\", \"category\": \"compiler\", \"name\": \"Compiler feature\", \"description\": \"Compiler\", \"spec_file\": \"compiler_spec.spl\", \"pure_status\": \"Planned\"}")
add_feature_from_json(TEST_FEATURE_DB, "{\"id\": \"feat_005\", \"category\": \"runtime\", \"name\": \"Runtime feature\", \"description\": \"Runtime\", \"spec_file\": \"runtime_spec.spl\", \"pure_status\": \"Planned\"}")
val json = get_features_by_category(TEST_FEATURE_DB, "compiler")
expect(json).to_contain("\"category\":\"compiler\"")
expect(json).to_contain("\"total\":1")
expect(json).to_contain("\"id\":\"feat_004\"")
expect(json.contains("\"id\":\"feat_005\"")).to_equal(false)
```

</details>

#### gets features by status

1. add feature from json

2. add feature from json


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
add_feature_from_json(TEST_FEATURE_DB, "{\"id\": \"feat_006\", \"category\": \"compiler\", \"name\": \"Planned feature\", \"description\": \"Planned\", \"spec_file\": \"planned_a_spec.spl\", \"pure_status\": \"Planned\"}")
add_feature_from_json(TEST_FEATURE_DB, "{\"id\": \"feat_007\", \"category\": \"compiler\", \"name\": \"Planned feature\", \"description\": \"Planned\", \"spec_file\": \"planned_spec.spl\", \"pure_status\": \"Planned\"}")
val json = get_features_by_status(TEST_FEATURE_DB, "Planned")
expect(json).to_contain("\"status\":\"Planned\"")
expect(json).to_contain("\"total\":2")
expect(json).to_contain("\"id\":\"feat_006\"")
expect(json).to_contain("\"id\":\"feat_007\"")
```

</details>

### Test Database MCP Resource

#### read operations

#### returns empty list for new database

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = get_all_tests(TEST_TEST_DB)
expect(json).to_contain("\"total\":0")
expect(json).to_contain("\"runs\":[]")
```

</details>

#### returns stats for empty database

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = get_test_stats(TEST_TEST_DB)
expect(json).to_contain("\"total_runs\":0")
expect(json).to_contain("\"total_tests\":0")
expect(json).to_contain("\"passed\":0")
```

</details>

#### test run lifecycle

#### starts a test run

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = start_test_run(TEST_TEST_DB)
expect(result).to_contain("\"success\":true")
expect(result).to_contain("\"run_id\":\"run_")
val json = get_all_tests(TEST_TEST_DB)
expect(json).to_contain("\"total\":1")
expect(json).to_contain("\"status\":\"running\"")
```

</details>

#### ends a test run

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val started = start_test_run(TEST_TEST_DB)
val run_id = json_string_value(started, "run_id")
val result = end_test_run(TEST_TEST_DB, run_id, "Completed")
expect(result).to_contain("\"success\":true")
val json = get_all_tests(TEST_TEST_DB)
expect(json).to_contain("\"status\":\"completed\"")
```

</details>

#### records test result

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val started = start_test_run(TEST_TEST_DB)
val run_id = json_string_value(started, "run_id")
val result = record_test_result(TEST_TEST_DB, run_id, "{\"test_name\": \"database_resource_spec\", \"status\": \"Passed\", \"duration_ms\": 12.5}")
expect(result).to_contain("\"success\":true")
expect(result).to_contain("\"test_name\":\"database_resource_spec\"")
val results = get_test_results(TEST_TEST_DB, run_id)
expect(results).to_contain("\"total\":1")
expect(results).to_contain("\"status\":\"passed\"")
```

</details>

#### analysis operations

#### returns empty flaky tests for new database

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = get_flaky_tests(TEST_TEST_DB)
expect(json).to_contain("\"count\":0")
expect(json).to_contain("\"tests\":[]")
```

</details>

#### returns empty slow tests for new database

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = get_slow_tests(TEST_TEST_DB, 1000.0)
expect(json).to_contain("\"count\":0")
expect(json).to_contain("\"tests\":[]")
```

</details>

### Database MCP Integration

#### atomic operations

#### database operations are atomic

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feature_json = "{\"id\": \"atomic_001\", \"category\": \"mcp\", \"name\": \"Atomic feature\", \"description\": \"Persisted\", \"spec_file\": \"atomic_spec.spl\", \"pure_status\": \"Planned\"}"
val result = add_feature_from_json(TEST_FEATURE_DB, feature_json)
expect(result).to_contain("\"success\":true")
val json = get_feature_by_id(TEST_FEATURE_DB, "atomic_001")
expect(json).to_contain("\"id\":\"atomic_001\"")
expect(json).to_contain("\"name\":\"Atomic feature\"")
```

</details>

#### JSON format

#### escapes special characters in JSON

1. add bug from json


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bug_json = "{\"id\": \"json_001\", \"severity\": \"P2\", \"status\": \"Open\", \"title\": \"JSON string field\", \"file\": \"json.spl\", \"line\": 1, \"reproducible_by\": \"json_spec\"}"
add_bug_from_json(TEST_BUG_DB, bug_json)
val json = get_bug_by_id(TEST_BUG_DB, "json_001")
expect(json).to_contain("\"title\":\"JSON string field\"")
expect(json).to_contain("\"description\":[]")
```

</details>

#### handles empty strings

1. add feature from json


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feature_json = "{\"id\": \"empty_001\", \"category\": \"\", \"name\": \"Empty strings\", \"description\": \"\", \"spec_file\": \"\", \"pure_status\": \"Planned\"}"
add_feature_from_json(TEST_FEATURE_DB, feature_json)
val json = get_feature_by_id(TEST_FEATURE_DB, "empty_001")
expect(json).to_contain("\"category\":\"\"")
expect(json).to_contain("\"description\":\"\"")
expect(json).to_contain("\"spec_file\":\"\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
