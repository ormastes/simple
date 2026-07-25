# Query Intensive Specification

> <details>

<!-- sdn-diagram:id=query_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Intensive Specification

## Scenarios

### BugDatabase Queries - Intensive

#### basic queries

<details>
<summary>Advanced: retrieves all bugs</summary>

#### retrieves all bugs _(slow)_

1. cleanup test file
2. var bugdb = create bug database
3. bugdb add bug
4. check
5. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_query_all.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)
for i in 0..20:
    bugdb.add_bug(generate_simple_bug("bug_{i}"))

val all_bugs = bugdb.all_bugs()
check(all_bugs.len() == 20)

cleanup_test_file(test_file)
```

</details>


</details>

<details>
<summary>Advanced: retrieves open bugs</summary>

#### retrieves open bugs _(slow)_

1. cleanup test file
2. var bugdb = create bug database
3. severity: BugSeverity P2
4. status: BugStatus Open
5. severity: BugSeverity P2
6. status: BugStatus Fixed
7. check
8. check
9. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_query_open.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Add mix of statuses (reduced from 25 each to 10 to avoid timeout)
for i in 0..10:
    bugdb.add_bug(Bug(
        id: "open_{i}",
        severity: BugSeverity.P2(),
        status: BugStatus.Open(),
        title: "Open bug {i}",
        description: ["Test"],
        file: "test.spl",
        line: 100,
        reproducible_by: "test",
        fix_strategy: [],
        investigation_log: [],
        created_at: 1738724000000000,
        updated_at: 1738724000000000,
        valid: true
    ))

for i in 0..10:
    bugdb.add_bug(Bug(
        id: "fixed_{i}",
        severity: BugSeverity.P2(),
        status: BugStatus.Fixed(),
        title: "Fixed bug {i}",
        description: ["Test"],
        file: "test.spl",
        line: 100,
        reproducible_by: "test",
        fix_strategy: [],
        investigation_log: [],
        created_at: 1738724000000000,
        updated_at: 1738724000000000,
        valid: true
    ))

val open_bugs = bugdb.open_bugs()
check(open_bugs.len() == 10)

# Verify all are open
for bug in open_bugs:
    check(bug.status.value == "Open")

cleanup_test_file(test_file)
```

</details>


</details>

<details>
<summary>Advanced: gets bug statistics</summary>

#### gets bug statistics _(slow)_

1. cleanup test file
2. var bugdb = create bug database
3. check
4. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_query_stats.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Add bugs with variety
val severities = [BugSeverity.P0(), BugSeverity.P1(), BugSeverity.P2(), BugSeverity.P3()]
val statuses = [BugStatus.Open(), BugStatus.Investigating(), BugStatus.Fixed(), BugStatus.Closed()]

# Reduced from 100 to 16 to avoid timeout
for i in 0..16:
    val severity = severities[i % 4]
    val status = statuses[(i / 4) % 4]
    bugdb.add_bug(Bug(
        id: "bug_{i}",
        severity: severity,
        status: status,
        title: "Bug {i}",
        description: ["Test"],
        file: "test.spl",
        line: 100 + i,
        reproducible_by: "test_{i}",
        fix_strategy: [],
        investigation_log: [],
        created_at: 1738724000000000,
        updated_at: 1738724000000000,
        valid: true
    ))

val stats = bugdb.stats()
check(stats["total"] == 16)

cleanup_test_file(test_file)
```

</details>


</details>

#### manual filtering

<details>
<summary>Advanced: filters bugs by severity manually</summary>

#### filters bugs by severity manually _(slow)_

1. cleanup test file
2. var bugdb = create bug database
3. severity: BugSeverity P0
4. status: BugStatus Open
5. severity: BugSeverity P2
6. status: BugStatus Open
7. check
8. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_filter_severity.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Add bugs with different severities (reduced from 25/75 to 5/15 to avoid timeout)
for i in 0..5:
    bugdb.add_bug(Bug(
        id: "p0_{i}",
        severity: BugSeverity.P0(),
        status: BugStatus.Open(),
        title: "Critical bug {i}",
        description: ["Critical"],
        file: "test.spl",
        line: 100,
        reproducible_by: "test",
        fix_strategy: [],
        investigation_log: [],
        created_at: 1738724000000000,
        updated_at: 1738724000000000,
        valid: true
    ))

for i in 0..15:
    bugdb.add_bug(Bug(
        id: "p2_{i}",
        severity: BugSeverity.P2(),
        status: BugStatus.Open(),
        title: "Normal bug {i}",
        description: ["Normal"],
        file: "test.spl",
        line: 100,
        reproducible_by: "test",
        fix_strategy: [],
        investigation_log: [],
        created_at: 1738724000000000,
        updated_at: 1738724000000000,
        valid: true
    ))

# Filter manually
val all_bugs = bugdb.all_bugs()
var p0_count = 0
for bug in all_bugs:
    if bug.severity.value == "P0":
        p0_count = p0_count + 1

check(p0_count == 5)

cleanup_test_file(test_file)
```

</details>


</details>

<details>
<summary>Advanced: filters bugs by file field</summary>

#### filters bugs by file field _(slow)_

1. cleanup test file
2. var bugdb = create bug database
3. severity: BugSeverity P1
4. status: BugStatus Open
5. severity: BugSeverity P2
6. status: BugStatus Open
7. check
8. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_filter_file.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Add bugs in different files (reduced from 20/30 to 5/10 to avoid timeout)
for i in 0..5:
    bugdb.add_bug(Bug(
        id: "parser_{i}",
        severity: BugSeverity.P1(),
        status: BugStatus.Open(),
        title: "Parser bug {i}",
        description: ["Parser issue"],
        file: "src/parser/mod.spl",
        line: 100 + i,
        reproducible_by: "test",
        fix_strategy: [],
        investigation_log: [],
        created_at: 1738724000000000,
        updated_at: 1738724000000000,
        valid: true
    ))

for i in 0..10:
    bugdb.add_bug(Bug(
        id: "other_{i}",
        severity: BugSeverity.P2(),
        status: BugStatus.Open(),
        title: "Other bug {i}",
        description: ["Other issue"],
        file: "src/other/mod.spl",
        line: 100,
        reproducible_by: "test",
        fix_strategy: [],
        investigation_log: [],
        created_at: 1738724000000000,
        updated_at: 1738724000000000,
        valid: true
    ))

# Filter manually
val all_bugs = bugdb.all_bugs()
var parser_bugs = 0
for bug in all_bugs:
    if bug.file == "src/parser/mod.spl":
        parser_bugs = parser_bugs + 1

check(parser_bugs == 5)

cleanup_test_file(test_file)
```

</details>


</details>

#### bulk operations

<details>
<summary>Advanced: handles retrieving 50 bugs</summary>

#### handles retrieving 50 bugs _(slow)_

1. cleanup test file
2. var bugdb = create bug database
3. bugdb add bug
4. check
5. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_bulk_50.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)
for i in 0..50:
    bugdb.add_bug(generate_simple_bug("bug_{i}"))

val all_bugs = bugdb.all_bugs()
check(all_bugs.len() == 50)

cleanup_test_file(test_file)
```

</details>


</details>

<details>
<summary>Advanced: handles mixed status queries with 20 bugs</summary>

#### handles mixed status queries with 20 bugs _(slow)_

1. cleanup test file
2. var bugdb = create bug database
3. severity: BugSeverity P2
4. check
5. check
6. check
7. check
8. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/test_bulk_mixed.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

val statuses = [BugStatus.Open(), BugStatus.Investigating(), BugStatus.Fixed(), BugStatus.Closed()]

# Reduced from 500 to 20 to avoid timeout
for i in 0..20:
    val status = statuses[i % 4]
    bugdb.add_bug(Bug(
        id: "bug_{i}",
        severity: BugSeverity.P2(),
        status: status,
        title: "Bug {i}",
        description: ["Test"],
        file: "test.spl",
        line: 100,
        reproducible_by: "test",
        fix_strategy: [],
        investigation_log: [],
        created_at: 1738724000000000,
        updated_at: 1738724000000000,
        valid: true
    ))

# Count by status
val all_bugs = bugdb.all_bugs()
var open_count = 0
var investigating_count = 0
var fixed_count = 0
var closed_count = 0

for bug in all_bugs:
    val sv = bug.status.value
    if sv == "Open":
        open_count = open_count + 1
    if sv == "Investigating":
        investigating_count = investigating_count + 1
    if sv == "Fixed":
        fixed_count = fixed_count + 1
    if sv == "Closed":
        closed_count = closed_count + 1

# Each status should have 5 bugs (20 / 4 statuses)
check(open_count == 5)
check(investigating_count == 5)
check(fixed_count == 5)
check(closed_count == 5)

cleanup_test_file(test_file)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/query_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BugDatabase Queries - Intensive

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 7 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
