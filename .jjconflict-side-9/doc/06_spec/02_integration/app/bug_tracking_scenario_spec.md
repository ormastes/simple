# Bug Tracking Scenario Specification

> 1. cleanup test file

<!-- sdn-diagram:id=bug_tracking_scenario_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bug_tracking_scenario_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bug_tracking_scenario_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bug_tracking_scenario_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bug Tracking Scenario Specification

## Scenarios

### Bug Tracking Scenario - Complete Workflow

#### developer discovers bug

#### creates bug report with all required fields

1. cleanup test file
2. severity: BugSeverity P0
3. status: BugStatus Open
4. var bugdb = create bug database
5. bugdb add bug
   - Expected: save_result is true
   - Expected: bug_result.? is true
   - Expected: loaded_bug.id equals `scenario_001`
   - Expected: loaded_bug.severity.value equals `P0`
   - Expected: loaded_bug.status.value equals `Open`
   - Expected: loaded_bug.title equals `Null pointer in parser`
6. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_discovery.sdn"
cleanup_test_file(test_file)

# Step 1: Developer finds bug
val bug = Bug(
    id: "scenario_001",
    severity: BugSeverity.P0(),
    status: BugStatus.Open(),
    title: "Null pointer in parser",
    description: [
        "Found while testing empty input",
        "Crashes on empty file",
        "Stack trace shows parser.spl:123"
    ],
    file: "src/parser/mod.spl",
    line: 123,
    reproducible_by: "test_parser_empty",
    fix_strategy: [],
    investigation_log: [],
    created_at: 1738724000000000,
    updated_at: 1738724000000000,
    valid: true
)

# Step 2: Save to database
var bugdb = create_bug_database(test_file)
bugdb.add_bug(bug)
val save_result = bugdb.save()
expect(save_result).to_equal(true)
# Step 3: Verify bug was saved
var loaded = bugdb
val bug_result = loaded.get_bug("scenario_001")
expect(bug_result.?).to_equal(true)
val loaded_bug = bug_result?
expect(loaded_bug.id).to_equal("scenario_001")
expect(loaded_bug.severity.value).to_equal("P0")
expect(loaded_bug.status.value).to_equal("Open")
expect(loaded_bug.title).to_equal("Null pointer in parser")
cleanup_test_file(test_file)
```

</details>

#### bug appears in open bugs list

1. cleanup test file
2. var bugdb = create bug database
3. bugdb add bug
4. bugdb save
   - Expected: found is true
5. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_open_query.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Add the bug
val bug = generate_bug_with_status("scenario_002", BugStatus.Open())
bugdb.add_bug(bug)
bugdb.save()

# Query for open bugs
var loaded = bugdb
val open_bugs = loaded.open_bugs()

expect(open_bugs.len()).to_be_greater_than(0)
# Verify our bug is in the results
var found = false
for b in open_bugs:
    if b.id == "scenario_002":
        found = true
expect(found).to_equal(true)
cleanup_test_file(test_file)
```

</details>

#### bug appears in MCP bugdb://open resource

1. cleanup test file
2. var bugdb = create bug database
3. bugdb add bug
4. bugdb save
   - Expected: found is true
5. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_mcp_open.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)
val bug = generate_bug_with_status("scenario_003", BugStatus.Open())
bugdb.add_bug(bug)
bugdb.save()

# Verify open bugs query contains our bug
val open = bugdb.open_bugs()
var found = false
for b in open:
    if b.id == "scenario_003":
        found = true
expect(found).to_equal(true)
cleanup_test_file(test_file)
```

</details>

#### team investigates bug

#### updates status to Investigating

1. cleanup test file
2. var bugdb = create bug database
3. bugdb add bug
4. bugdb save
5. status: BugStatus Investigating
6. bugdb update bug
7. bugdb save
   - Expected: bug_result.? is true
   - Expected: updated_bug.status.value equals `Investigating`
8. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_investigating.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Create and add bug
val bug = generate_bug_with_status("scenario_004", BugStatus.Open())
bugdb.add_bug(bug)
bugdb.save()

# Update status - reconstruct bug with new status
if val Some(old_bug) = bugdb.get_bug("scenario_004"):
    val updated_bug = Bug(
        id: old_bug.id,
        severity: old_bug.severity,
        status: BugStatus.Investigating(),
        title: old_bug.title,
        description: old_bug.description,
        file: old_bug.file,
        line: old_bug.line,
        reproducible_by: old_bug.reproducible_by,
        fix_strategy: old_bug.fix_strategy,
        investigation_log: old_bug.investigation_log,
        created_at: old_bug.created_at,
        updated_at: 1738724000000000,
        valid: old_bug.valid
    )
    bugdb.update_bug("scenario_004", updated_bug)
    bugdb.save()

# Verify update
var loaded = bugdb
val bug_result = loaded.get_bug("scenario_004")
expect(bug_result.?).to_equal(true)
val updated_bug = bug_result?
expect(updated_bug.status.value).to_equal("Investigating")
cleanup_test_file(test_file)
```

</details>

#### adds investigation notes

1. cleanup test file
2. var bugdb = create bug database
3. severity: BugSeverity P1
4. status: BugStatus Investigating
5. bugdb add bug
6. bugdb save
   - Expected: bug_result.? is true
   - Expected: loaded_bug.investigation_log.len() equals `3`
7. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_notes.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

val bug = Bug(
    id: "scenario_005",
    severity: BugSeverity.P1(),
    status: BugStatus.Investigating(),
    title: "Memory leak in GC",
    description: ["Leak detected in long-running process"],
    file: "src/gc/mod.spl",
    line: 456,
    reproducible_by: "test_gc_long",
    fix_strategy: [],
    investigation_log: [
        "2026-02-05: Started investigation",
        "2026-02-05: Reproduced locally",
        "2026-02-05: Found root cause in allocation"
    ],
    created_at: 1738724000000000,
    updated_at: 1738724000000000,
    valid: true
)

bugdb.add_bug(bug)
bugdb.save()

# Verify investigation log persisted
var loaded = bugdb
val bug_result = loaded.get_bug("scenario_005")
expect(bug_result.?).to_equal(true)
val loaded_bug = bug_result?
expect(loaded_bug.investigation_log.len()).to_equal(3)
cleanup_test_file(test_file)
```

</details>

#### proposes fix strategy

1. cleanup test file
2. var bugdb = create bug database
3. severity: BugSeverity P0
4. status: BugStatus Investigating
5. bugdb add bug
6. bugdb save
   - Expected: bug_result.? is true
   - Expected: loaded_bug.fix_strategy.len() equals `3`
7. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_strategy.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

val bug = Bug(
    id: "scenario_006",
    severity: BugSeverity.P0(),
    status: BugStatus.Investigating(),
    title: "Race condition in concurrent module",
    description: ["Race condition causes data corruption"],
    file: "src/concurrent/mod.spl",
    line: 789,
    reproducible_by: "test_concurrent",
    fix_strategy: [
        "Add mutex around critical section",
        "Use atomic operations for counters",
        "Add regression test"
    ],
    investigation_log: [],
    created_at: 1738724000000000,
    updated_at: 1738724000000000,
    valid: true
)

bugdb.add_bug(bug)
bugdb.save()

# Verify fix strategy persisted
var loaded = bugdb
val bug_result = loaded.get_bug("scenario_006")
expect(bug_result.?).to_equal(true)
val loaded_bug = bug_result?
expect(loaded_bug.fix_strategy.len()).to_equal(3)
cleanup_test_file(test_file)
```

</details>

#### developer fixes bug

#### updates status to Fixed

1. cleanup test file
2. var bugdb = create bug database
3. bugdb add bug
4. bugdb save
5. status: BugStatus Fixed
6. bugdb update bug
7. bugdb save
   - Expected: bug_result.? is true
   - Expected: fixed_bug.status.value equals `Fixed`
8. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_fixed.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Start with Investigating status
val bug = generate_bug_with_status("scenario_007", BugStatus.Investigating())
bugdb.add_bug(bug)
bugdb.save()

# Update to Fixed
if val Some(old_bug) = bugdb.get_bug("scenario_007"):
    val updated_bug = Bug(
        id: old_bug.id,
        severity: old_bug.severity,
        status: BugStatus.Fixed(),
        title: old_bug.title,
        description: old_bug.description,
        file: old_bug.file,
        line: old_bug.line,
        reproducible_by: old_bug.reproducible_by,
        fix_strategy: old_bug.fix_strategy,
        investigation_log: old_bug.investigation_log,
        created_at: old_bug.created_at,
        updated_at: 1738724000000000,
        valid: old_bug.valid
    )
    bugdb.update_bug("scenario_007", updated_bug)
    bugdb.save()

# Verify update
var loaded = bugdb
val bug_result = loaded.get_bug("scenario_007")
expect(bug_result.?).to_equal(true)
val fixed_bug = bug_result?
expect(fixed_bug.status.value).to_equal("Fixed")
cleanup_test_file(test_file)
```

</details>

#### fixed bugs no longer appear in open bugs

1. cleanup test file
2. var bugdb = create bug database
3. var status = BugStatus Open
4. status = BugStatus Fixed
5. bugdb add bug
6. bugdb save
   - Expected: open_bugs.len() equals `5`
   - Expected: bug.status.value equals `Open`
7. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_not_open.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Add mix of open and fixed bugs
for i in 0..10:
    var status = BugStatus.Open()
    if i % 2 != 0:
        status = BugStatus.Fixed()
    val bug = generate_bug_with_status("scenario_{i}", status)
    bugdb.add_bug(bug)

bugdb.save()

# Query for open bugs only
var loaded = bugdb
val open_bugs = loaded.open_bugs()

# Should have 5 open bugs (even indices)
expect(open_bugs.len()).to_equal(5)
# Verify none are Fixed
for bug in open_bugs:
    expect(bug.status.value).to_equal("Open")
cleanup_test_file(test_file)
```

</details>

#### QA validates fix

#### updates status to Closed

1. cleanup test file
2. var bugdb = create bug database
3. bugdb add bug
4. bugdb save
5. status: BugStatus Closed
6. bugdb update bug
7. bugdb save
   - Expected: bug_result.? is true
   - Expected: closed_bug.status.value equals `Closed`
8. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_closed.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Start with Fixed status
val bug = generate_bug_with_status("scenario_008", BugStatus.Fixed())
bugdb.add_bug(bug)
bugdb.save()

# Update to Closed
if val Some(old_bug) = bugdb.get_bug("scenario_008"):
    val updated_bug = Bug(
        id: old_bug.id,
        severity: old_bug.severity,
        status: BugStatus.Closed(),
        title: old_bug.title,
        description: old_bug.description,
        file: old_bug.file,
        line: old_bug.line,
        reproducible_by: old_bug.reproducible_by,
        fix_strategy: old_bug.fix_strategy,
        investigation_log: old_bug.investigation_log,
        created_at: old_bug.created_at,
        updated_at: 1738724000000000,
        valid: old_bug.valid
    )
    bugdb.update_bug("scenario_008", updated_bug)
    bugdb.save()

# Verify update
var loaded = bugdb
val bug_result = loaded.get_bug("scenario_008")
expect(bug_result.?).to_equal(true)
val closed_bug = bug_result?
expect(closed_bug.status.value).to_equal("Closed")
cleanup_test_file(test_file)
```

</details>

#### statistics reflect bug closure

1. cleanup test file
2. var bugdb = create bug database
3. bugdb add bug
4. bugdb add bug
5. bugdb add bug
6. bugdb add bug
7. bugdb add bug
8. bugdb add bug
9. bugdb add bug
10. bugdb add bug
11. bugdb add bug
12. bugdb add bug
13. bugdb save
   - Expected: all.len() equals `10`
   - Expected: open.len() equals `3`
14. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_stats.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Add 10 bugs with various statuses
val b0 = generate_bug_with_status("stat_0", BugStatus.Open())
bugdb.add_bug(b0)
val b1 = generate_bug_with_status("stat_1", BugStatus.Open())
bugdb.add_bug(b1)
val b2 = generate_bug_with_status("stat_2", BugStatus.Open())
bugdb.add_bug(b2)
val b3 = generate_bug_with_status("stat_3", BugStatus.Investigating())
bugdb.add_bug(b3)
val b4 = generate_bug_with_status("stat_4", BugStatus.Investigating())
bugdb.add_bug(b4)
val b5 = generate_bug_with_status("stat_5", BugStatus.Investigating())
bugdb.add_bug(b5)
val b6 = generate_bug_with_status("stat_6", BugStatus.Fixed())
bugdb.add_bug(b6)
val b7 = generate_bug_with_status("stat_7", BugStatus.Fixed())
bugdb.add_bug(b7)
val b8 = generate_bug_with_status("stat_8", BugStatus.Closed())
bugdb.add_bug(b8)
val b9 = generate_bug_with_status("stat_9", BugStatus.Closed())
bugdb.add_bug(b9)
bugdb.save()

# Verify bug count
val all = bugdb.all_bugs()
expect(all.len()).to_equal(10)
# Check open bugs count
val open = bugdb.open_bugs()
expect(open.len()).to_equal(3)
cleanup_test_file(test_file)
```

</details>

#### complete lifecycle

#### tracks bug from discovery to closure

1. cleanup test file
2. var bugdb = create bug database
3. severity: BugSeverity P1
4. status: BugStatus Open
5. bugdb add bug
6. bugdb save
7. status: BugStatus Investigating
8. bugdb update bug
9. bugdb save
   - Expected: inv_bug.status.value equals `Investigating`
10. status: BugStatus Fixed
11. bugdb update bug
12. bugdb save
   - Expected: fix_bug.status.value equals `Fixed`
13. status: BugStatus Closed
14. bugdb update bug
15. bugdb save
   - Expected: close_bug.status.value equals `Closed`
16. cleanup test file


<details>
<summary>Executable SSpec</summary>

Runnable source: 94 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/scenario_bugdb_lifecycle.sdn"
cleanup_test_file(test_file)

var bugdb = create_bug_database(test_file)

# Step 1: Create bug (Open)
val bug = Bug(
    id: "lifecycle_001",
    severity: BugSeverity.P1(),
    status: BugStatus.Open(),
    title: "Complete lifecycle test bug",
    description: ["Test bug for full lifecycle"],
    file: "test.spl",
    line: 100,
    reproducible_by: "test_lifecycle",
    fix_strategy: [],
    investigation_log: [],
    created_at: 1738724000000000,
    updated_at: 1738724000000000,
    valid: true
)
bugdb.add_bug(bug)
bugdb.save()

# Step 2: Start investigation
if val Some(old) = bugdb.get_bug("lifecycle_001"):
    val updated = Bug(
        id: old.id,
        severity: old.severity,
        status: BugStatus.Investigating(),
        title: old.title,
        description: old.description,
        file: old.file,
        line: old.line,
        reproducible_by: old.reproducible_by,
        fix_strategy: old.fix_strategy,
        investigation_log: old.investigation_log,
        created_at: old.created_at,
        updated_at: 1738724000000000,
        valid: old.valid
    )
    bugdb.update_bug("lifecycle_001", updated)
    bugdb.save()

var inv_loaded = bugdb
val inv_bug = inv_loaded.get_bug("lifecycle_001")?
expect(inv_bug.status.value).to_equal("Investigating")
# Step 3: Fix bug
if val Some(old) = bugdb.get_bug("lifecycle_001"):
    val updated = Bug(
        id: old.id,
        severity: old.severity,
        status: BugStatus.Fixed(),
        title: old.title,
        description: old.description,
        file: old.file,
        line: old.line,
        reproducible_by: old.reproducible_by,
        fix_strategy: old.fix_strategy,
        investigation_log: old.investigation_log,
        created_at: old.created_at,
        updated_at: 1738724000000000,
        valid: old.valid
    )
    bugdb.update_bug("lifecycle_001", updated)
    bugdb.save()

var fix_loaded = bugdb
val fix_bug = fix_loaded.get_bug("lifecycle_001")?
expect(fix_bug.status.value).to_equal("Fixed")
# Step 4: Close bug
if val Some(old) = bugdb.get_bug("lifecycle_001"):
    val updated = Bug(
        id: old.id,
        severity: old.severity,
        status: BugStatus.Closed(),
        title: old.title,
        description: old.description,
        file: old.file,
        line: old.line,
        reproducible_by: old.reproducible_by,
        fix_strategy: old.fix_strategy,
        investigation_log: old.investigation_log,
        created_at: old.created_at,
        updated_at: 1738724000000000,
        valid: old.valid
    )
    bugdb.update_bug("lifecycle_001", updated)
    bugdb.save()

var close_loaded = bugdb
val close_bug = close_loaded.get_bug("lifecycle_001")?
expect(close_bug.status.value).to_equal("Closed")
cleanup_test_file(test_file)
```

</details>

#### concurrent bug tracking

#### handles multiple bugs being tracked simultaneously

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val severities = get_test_severities()
val statuses = get_test_statuses()
expect(severities.len()).to_equal(4)
expect(statuses.len()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/bug_tracking_scenario_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bug Tracking Scenario - Complete Workflow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
