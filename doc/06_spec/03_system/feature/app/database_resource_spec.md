# MCP Database Resource

> Tests the MCP database resource interface for querying bug, test, and feature databases through MCP tools. Verifies that database resources are correctly exposed, queryable, and return well-formed results via the MCP protocol.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP database resource interface for querying bug, test, and feature
databases through MCP tools. Verifies that database resources are correctly
exposed, queryable, and return well-formed results via the MCP protocol.

## Scenarios

### Bug Database MCP Resource

#### read operations

#### returns JSON error for missing database

- returns JSON error for missing database


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns JSON error for missing database")
val json = get_all_bugs(TEST_BUG_DB)
expect(json).to_contain("\"error\"")
expect(json).to_contain("Database not found")
```

</details>

#### returns stats error for missing database

- returns stats error for missing database


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns stats error for missing database")
val json = get_bug_stats(TEST_BUG_DB)
expect(json).to_contain("\"error\"")
expect(json).to_contain("Database not found")
```

</details>

#### returns error for non-existent bug

- returns error for non-existent bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns error for non-existent bug")
val json = get_bug_by_id(TEST_BUG_DB, "nonexistent")
expect(json).to_contain("\"error\"")
expect(json).to_contain("not found")
```

</details>

#### write operations

#### adds bug via JSON

- adds bug via JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds bug via JSON")
val bug_json = "{\"id\": \"test_001\", \"severity\": \"P2\", \"status\": \"Open\", \"title\": \"Test bug\", \"file\": \"test.spl\", \"line\": 42, \"reproducible_by\": \"test_spec\"}"
val result = add_bug_from_json(TEST_BUG_DB, bug_json)
expect(result).to_contain("\"success\":true")
expect(result).to_contain("\"id\":\"test_001\"")
```

</details>

#### retrieves added bug

- retrieves added bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retrieves added bug")
val bug_json = "{\"id\": \"test_002\", \"severity\": \"P1\", \"status\": \"Open\", \"title\": \"Critical bug\", \"file\": \"critical.spl\", \"line\": 100, \"reproducible_by\": \"critical_spec\"}"
add_bug_from_json(TEST_BUG_DB, bug_json)
val json = get_bug_by_id(TEST_BUG_DB, "test_002")
expect(json).to_contain("\"id\":\"test_002\"")
```

</details>

#### updates bug status

- updates bug status


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("updates bug status")
val bug_json = "{\"id\": \"test_003\", \"severity\": \"P2\", \"status\": \"Open\", \"title\": \"Bug to fix\", \"file\": \"fix.spl\", \"line\": 50, \"reproducible_by\": \"fix_spec\"}"
add_bug_from_json(TEST_BUG_DB, bug_json)
val update_json = "{\"status\": \"Fixed\"}"
val result = update_bug_from_json(TEST_BUG_DB, "test_003", update_json)
expect(result).to_contain("\"success\":true")
```

</details>

#### fails to add bug without id

- fails to add bug without id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails to add bug without id")
val bad_json = "{\"title\": \"No ID bug\"}"
val result = add_bug_from_json(TEST_BUG_DB, bad_json)
expect(result).to_contain("\"error\"")
```

</details>

#### query operations

#### gets open bugs only

- gets open bugs only
   - Expected: json does not contain `"id":"fixed_001"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets open bugs only")
add_bug_from_json(TEST_BUG_DB, "{\"id\": \"open_001\", \"severity\": \"P2\", \"status\": \"Open\", \"title\": \"Open bug\"}")
add_bug_from_json(TEST_BUG_DB, "{\"id\": \"fixed_001\", \"severity\": \"P2\", \"status\": \"Fixed\", \"title\": \"Fixed bug\"}")
val json = get_open_bugs(TEST_BUG_DB)
expect(json).to_contain("\"total\":1")
expect(json).to_contain("\"id\":\"open_001\"")
expect(json.contains("\"id\":\"fixed_001\"")).to_equal(false)
```

</details>

#### gets critical bugs only

- gets critical bugs only
   - Expected: json does not contain `"id":"normal_001"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets critical bugs only")
add_bug_from_json(TEST_BUG_DB, "{\"id\": \"critical_001\", \"severity\": \"P1\", \"status\": \"Open\", \"title\": \"Critical bug\"}")
add_bug_from_json(TEST_BUG_DB, "{\"id\": \"normal_001\", \"severity\": \"P3\", \"status\": \"Open\", \"title\": \"Normal bug\"}")
val json = get_critical_bugs(TEST_BUG_DB)
expect(json).to_contain("\"total\":1")
expect(json).to_contain("\"id\":\"critical_001\"")
expect(json.contains("\"id\":\"normal_001\"")).to_equal(false)
```

</details>

#### calculates correct stats

- calculates correct stats


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calculates correct stats")
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

- returns empty list for new database


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty list for new database")
val json = get_all_features(TEST_FEATURE_DB)
expect(json).to_contain("\"total\":0")
expect(json).to_contain("\"features\":[]")
```

</details>

#### returns stats for empty database

- returns stats for empty database


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns stats for empty database")
val json = get_feature_stats(TEST_FEATURE_DB)
expect(json).to_contain("\"total\":0")
expect(json).to_contain("\"done\":0")
expect(json).to_contain("\"planned\":0")
```

</details>

#### write operations

#### adds feature via JSON

- adds feature via JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds feature via JSON")
val feature_json = "{\"id\": \"feat_001\", \"category\": \"compiler\", \"name\": \"Parser feature\", \"description\": \"Parse expressions\", \"spec_file\": \"parser_spec.spl\", \"pure_status\": \"Planned\", \"hybrid_status\": \"Planned\", \"llvm_status\": \"Planned\"}"
val result = add_feature_from_json(TEST_FEATURE_DB, feature_json)
expect(result).to_contain("\"success\":true")
expect(result).to_contain("\"id\":\"feat_001\"")
```

</details>

#### retrieves added feature

- retrieves added feature


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retrieves added feature")
val feature_json = "{\"id\": \"feat_002\", \"category\": \"runtime\", \"name\": \"Runtime feature\", \"description\": \"Run code\", \"spec_file\": \"runtime_spec.spl\", \"pure_status\": \"Planned\", \"hybrid_status\": \"Planned\", \"llvm_status\": \"Planned\"}"
add_feature_from_json(TEST_FEATURE_DB, feature_json)
val json = get_feature_by_id(TEST_FEATURE_DB, "feat_002")
expect(json).to_contain("\"id\":\"feat_002\"")
expect(json).to_contain("\"category\":\"runtime\"")
expect(json).to_contain("\"pure_status\":\"planned\"")
```

</details>

#### updates feature status

- updates feature status


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("updates feature status")
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

- gets features by category
   - Expected: json does not contain `"id":"feat_005"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets features by category")
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

- gets features by status


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets features by status")
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

- returns empty list for new database


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty list for new database")
val json = get_all_tests(TEST_TEST_DB)
expect(json).to_contain("\"total\":0")
expect(json).to_contain("\"runs\":[]")
```

</details>

#### returns stats for empty database

- returns stats for empty database


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns stats for empty database")
val json = get_test_stats(TEST_TEST_DB)
expect(json).to_contain("\"total_runs\":0")
expect(json).to_contain("\"total_tests\":0")
expect(json).to_contain("\"passed\":0")
```

</details>

#### test run lifecycle

#### starts a test run

- starts a test run


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts a test run")
val result = start_test_run(TEST_TEST_DB)
expect(result).to_contain("\"success\":true")
expect(result).to_contain("\"run_id\":\"run_")
val json = get_all_tests(TEST_TEST_DB)
expect(json).to_contain("\"total\":1")
expect(json).to_contain("\"status\":\"running\"")
```

</details>

#### ends a test run

- ends a test run


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ends a test run")
val started = start_test_run(TEST_TEST_DB)
val run_id = json_string_value(started, "run_id")
val result = end_test_run(TEST_TEST_DB, run_id, "Completed")
expect(result).to_contain("\"success\":true")
val json = get_all_tests(TEST_TEST_DB)
expect(json).to_contain("\"status\":\"completed\"")
```

</details>

#### records test result

- records test result


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records test result")
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

- returns empty flaky tests for new database


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty flaky tests for new database")
val json = get_flaky_tests(TEST_TEST_DB)
expect(json).to_contain("\"count\":0")
expect(json).to_contain("\"tests\":[]")
```

</details>

#### returns empty slow tests for new database

- returns empty slow tests for new database


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty slow tests for new database")
val json = get_slow_tests(TEST_TEST_DB, 1000.0)
expect(json).to_contain("\"count\":0")
expect(json).to_contain("\"tests\":[]")
```

</details>

### Database MCP Integration

#### atomic operations

#### database operations are atomic

- database operations are atomic


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("database operations are atomic")
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

- escapes special characters in JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes special characters in JSON")
val bug_json = "{\"id\": \"json_001\", \"severity\": \"P2\", \"status\": \"Open\", \"title\": \"JSON string field\", \"file\": \"json.spl\", \"line\": 1, \"reproducible_by\": \"json_spec\"}"
add_bug_from_json(TEST_BUG_DB, bug_json)
val json = get_bug_by_id(TEST_BUG_DB, "json_001")
expect(json).to_contain("\"title\":\"JSON string field\"")
expect(json).to_contain("\"description\":[]")
```

</details>

#### handles empty strings

- handles empty strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty strings")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2831b0609a8a126e22c20e48cfe9c3e64440a6315d78b0c35f9d50ecf5deb532`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2831b0609a8a126e22c20e48cfe9c3e64440a6315d78b0c35f9d50ecf5deb532`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2831b0609a8a126e22c20e48cfe9c3e64440a6315d78b0c35f9d50ecf5deb532`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/app/database_resource_spec.spl
mirror: doc/06_spec/03_system/feature/app/database_resource_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/database_resource_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/database_resource_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/database_resource_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns JSON error for missing database' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/database_resource_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns stats error for missing database' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/database_resource_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns error for non-existent bug' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
