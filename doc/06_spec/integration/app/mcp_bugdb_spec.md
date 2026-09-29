# Mcp Bugdb Specification

> Tests covering MCP Bug Database Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Bugdb Specification

## Scenarios

### MCP Bug Database Integration

#### gets all bugs as JSON

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gets all bugs as JSON
   - Expected: json contains `mcp_test_001`
   - Expected: json contains `Critical bug`
   - Expected: json contains `"total":1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets all bugs as JSON")
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

- gets open bugs only
   - Expected: json contains `open_001`
   - Expected: not json contains `fixed_001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets open bugs only")
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

- gets critical bugs (P0 and P1)
   - Expected: json contains `p0_001`
   - Expected: json contains `p1_001`
   - Expected: not json contains `p2_001`
   - Expected: json contains `"total":2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 67 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets critical bugs (P0 and P1)")
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

- gets bug statistics
   - Expected: json contains `"total":5`
   - Expected: json contains `"open":3`
   - Expected: json contains `"fixed":2`
   - Expected: json contains `"p0":2`
   - Expected: json contains `"health":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets bug statistics")
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

- handles missing database gracefully
   - Expected: json contains `"error":`
   - Expected: json contains `Database not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles missing database gracefully")
val json = get_all_bugs("/nonexistent/path.sdn")

# Should return error JSON
expect(json.contains("\"error\":")).to_equal(true)
expect(json.contains("Database not found")).to_equal(true)
```

</details>

#### escapes JSON special characters

- escapes JSON special characters
   - Expected: json contains `\\"`
   - Expected: json contains `\\\\`
   - Expected: json contains `\\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("escapes JSON special characters")
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
| Source | `test/integration/app/mcp_bugdb_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Bug Database Integration.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a2c72ba5fbeb053d73a7a476d5534969bcb293387788b336fd39bc7c6aa25849`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2c72ba5fbeb053d73a7a476d5534969bcb293387788b336fd39bc7c6aa25849`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2c72ba5fbeb053d73a7a476d5534969bcb293387788b336fd39bc7c6aa25849`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/mcp_bugdb_spec.spl
mirror: doc/06_spec/integration/app/mcp_bugdb_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/mcp_bugdb_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/mcp_bugdb_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/mcp_bugdb_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets all bugs as JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/mcp_bugdb_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets open bugs only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/mcp_bugdb_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets critical bugs (P0 and P1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
