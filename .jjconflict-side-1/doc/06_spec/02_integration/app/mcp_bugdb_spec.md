# Mcp Bugdb Specification

> 1. var bugdb = create bug database

<!-- sdn-diagram:id=mcp_bugdb_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_bugdb_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_bugdb_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_bugdb_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Bugdb Specification

## Scenarios

### MCP Bug Database Integration

#### gets all bugs as JSON

1. var bugdb = create bug database
2. bugdb add bug
3. bugdb save
   - Expected: json contains `mcp_test_001`
   - Expected: json contains `Critical bug`
   - Expected: json contains `"total":1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create test database
val db_path = "/tmp/test_mcp_all_bugs.sdn"
var bugdb = create_bug_database(db_path)

# Add test bugs
val bug1 = Bug(
    id: "mcp_test_001",
    severity: BugSeverity.P0,
    status: BugStatus.Open,
    title: "Critical bug",
    description: ["Critical issue"],
    file: "test.spl",
    line: 1,
    reproducible_by: "test_1",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

bugdb.add_bug(bug1)
bugdb.save()

# Get bugs via MCP resource
val json = get_all_bugs(db_path)

# Verify JSON contains bug
expect(json.contains("mcp_test_001")).to_equal(true)
expect(json.contains("Critical bug")).to_equal(true)
expect(json.contains("\"total\":1")).to_equal(true)
```

</details>

#### gets open bugs only

1. var bugdb = create bug database
2. bugdb add bug
3. bugdb add bug
4. bugdb save
   - Expected: json contains `open_001`
   - Expected: not json contains `fixed_001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/test_mcp_open_bugs.sdn"
var bugdb = create_bug_database(db_path)

# Add open and fixed bugs
val open_bug = Bug(
    id: "open_001",
    severity: BugSeverity.P1,
    status: BugStatus.Open,
    title: "Open bug",
    description: ["Open"],
    file: "test.spl",
    line: 1,
    reproducible_by: "test",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

val fixed_bug = Bug(
    id: "fixed_001",
    severity: BugSeverity.P2,
    status: BugStatus.Fixed,
    title: "Fixed bug",
    description: ["Fixed"],
    file: "test.spl",
    line: 2,
    reproducible_by: "test",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

bugdb.add_bug(open_bug)
bugdb.add_bug(fixed_bug)
bugdb.save()

# Get open bugs
val json = get_open_bugs(db_path)

# Should contain open bug but not fixed
expect(json.contains("open_001")).to_equal(true)
expect(not json.contains("fixed_001")).to_equal(true)
```

</details>

#### gets critical bugs (P0 and P1)

1. var bugdb = create bug database
2. bugdb add bug
3. bugdb add bug
4. bugdb add bug
5. bugdb save
   - Expected: json contains `p0_001`
   - Expected: json contains `p1_001`
   - Expected: not json contains `p2_001`
   - Expected: json contains `"total":2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/test_mcp_critical.sdn"
var bugdb = create_bug_database(db_path)

# Add bugs of different severities
val p0_bug = Bug(
    id: "p0_001",
    severity: BugSeverity.P0,
    status: BugStatus.Open,
    title: "P0 bug",
    description: ["Critical"],
    file: "test.spl",
    line: 1,
    reproducible_by: "test",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

val p1_bug = Bug(
    id: "p1_001",
    severity: BugSeverity.P1,
    status: BugStatus.Open,
    title: "P1 bug",
    description: ["High priority"],
    file: "test.spl",
    line: 2,
    reproducible_by: "test",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

val p2_bug = Bug(
    id: "p2_001",
    severity: BugSeverity.P2,
    status: BugStatus.Open,
    title: "P2 bug",
    description: ["Medium priority"],
    file: "test.spl",
    line: 3,
    reproducible_by: "test",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

bugdb.add_bug(p0_bug)
bugdb.add_bug(p1_bug)
bugdb.add_bug(p2_bug)
bugdb.save()

# Get critical bugs
val json = get_critical_bugs(db_path)

# Should contain P0 and P1 but not P2
expect(json.contains("p0_001")).to_equal(true)
expect(json.contains("p1_001")).to_equal(true)
expect(not json.contains("p2_001")).to_equal(true)
expect(json.contains("\"total\":2")).to_equal(true)
```

</details>

#### gets bug statistics

1. var bugdb = create bug database
2. bugdb add bug
3. bugdb save
   - Expected: json contains `"total":5`
   - Expected: json contains `"open":3`
   - Expected: json contains `"fixed":2`
   - Expected: json contains `"p0":2`
   - Expected: json contains `"health":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/test_mcp_stats.sdn"
var bugdb = create_bug_database(db_path)

# Add various bugs
for i in 0..5:
    val sev = if i < 2: BugSeverity.P0 else: BugSeverity.P2
    val status = if i < 3: BugStatus.Open else: BugStatus.Fixed

    val bug = Bug(
        id: "bug_{i}",
        severity: sev,
        status: status,
        title: "Bug {i}",
        description: ["Test bug {i}"],
        file: "test.spl",
        line: i,
        reproducible_by: "test",
        fix_strategy: [],
        investigation_log: [],
        created_at: "2026-02-05",
        updated_at: "2026-02-05",
        valid: true
    )

    bugdb.add_bug(bug)

bugdb.save()

# Get statistics
val json = get_bug_stats(db_path)

# Verify stats
expect(json.contains("\"total\":5")).to_equal(true)
expect(json.contains("\"open\":3")).to_equal(true)
expect(json.contains("\"fixed\":2")).to_equal(true)
expect(json.contains("\"p0\":2")).to_equal(true)
expect(json.contains("\"health\":")).to_equal(true)
```

</details>

#### handles missing database gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = get_all_bugs("/nonexistent/path.sdn")

# Should return error JSON
expect(json.contains("\"error\":")).to_equal(true)
expect(json.contains("Database not found")).to_equal(true)
```

</details>

#### escapes JSON special characters

1. var bugdb = create bug database
2. bugdb add bug
3. bugdb save
   - Expected: json contains `\\"`
   - Expected: json contains `\\\\`
   - Expected: json contains `\\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/test_mcp_escape.sdn"
var bugdb = create_bug_database(db_path)

# Add bug with special characters
val bug = Bug(
    id: "escape_001",
    severity: BugSeverity.P1,
    status: BugStatus.Open,
    title: "Bug with \"quotes\" and \\backslashes",
    description: ["Line 1\nLine 2", "Tab\there"],
    file: "test.spl",
    line: 1,
    reproducible_by: "test",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

bugdb.add_bug(bug)
bugdb.save()

# Get bugs as JSON
val json = get_all_bugs(db_path)

# Verify escaping
expect(json.contains("\\\"")).to_equal(true)  # Escaped quotes
expect(json.contains("\\\\")).to_equal(true)  # Escaped backslashes
expect(json.contains("\\t")).to_equal(true)   # Escaped tab
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/mcp_bugdb_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Bug Database Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
