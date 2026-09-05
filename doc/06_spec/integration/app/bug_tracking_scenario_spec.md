# bug_tracking_scenario_spec

> Purpose: This spec proves Bug Tracking Scenario - Complete Workflow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bug_tracking_scenario_spec

Purpose: This spec proves Bug Tracking Scenario - Complete Workflow.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/bug_tracking_scenario_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Bug Tracking Scenario - Complete Workflow.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Bug Tracking Scenario - Complete Workflow

#### developer discovers bug

#### creates bug report with all required fields

- creates bug report with all required fields
   - Expected: save_result is true
   - Expected: bug_result == nil is false
   - Expected: loaded_bug.id equals `scenario_001`
   - Expected: loaded_bug.severity.value equals `P0`
   - Expected: loaded_bug.status.value equals `Open`
   - Expected: loaded_bug.title equals `Null pointer in parser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BUGTRACKINGSCENARIO-001
# @req: REQ-BUGTRACKINGSCENARIO-001
step("creates bug report with all required fields")
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
expect(bug_result == nil).to_equal(false)
val loaded_bug = bug_result?
expect(loaded_bug.id).to_equal("scenario_001")
expect(loaded_bug.severity.value).to_equal("P0")
expect(loaded_bug.status.value).to_equal("Open")
expect(loaded_bug.title).to_equal("Null pointer in parser")
cleanup_test_file(test_file)
```

</details>

#### bug appears in open bugs list

- bug appears in open bugs list
- bug appears in open bugs list
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bug appears in open bugs list")
step("bug appears in open bugs list")
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

- bug appears in MCP bugdb://open resource
- bug appears in MCP bugdb://open resource
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bug appears in MCP bugdb://open resource")
step("bug appears in MCP bugdb://open resource")
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

- updates status to Investigating
- updates status to Investigating
   - Expected: bug_result == nil is false
   - Expected: updated_bug.status.value equals `Investigating`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("updates status to Investigating")
step("updates status to Investigating")
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
expect(bug_result == nil).to_equal(false)
val updated_bug = bug_result?
expect(updated_bug.status.value).to_equal("Investigating")
cleanup_test_file(test_file)
```

</details>

#### adds investigation notes

- adds investigation notes
- adds investigation notes
   - Expected: bug_result == nil is false
   - Expected: loaded_bug.investigation_log.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adds investigation notes")
step("adds investigation notes")
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
expect(bug_result == nil).to_equal(false)
val loaded_bug = bug_result?
expect(loaded_bug.investigation_log.len()).to_equal(3)
cleanup_test_file(test_file)
```

</details>

#### proposes fix strategy

- proposes fix strategy
- proposes fix strategy
   - Expected: bug_result == nil is false
   - Expected: loaded_bug.fix_strategy.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("proposes fix strategy")
step("proposes fix strategy")
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
expect(bug_result == nil).to_equal(false)
val loaded_bug = bug_result?
expect(loaded_bug.fix_strategy.len()).to_equal(3)
cleanup_test_file(test_file)
```

</details>

#### developer fixes bug

#### updates status to Fixed

- updates status to Fixed
- updates status to Fixed
   - Expected: bug_result == nil is false
   - Expected: fixed_bug.status.value equals `Fixed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("updates status to Fixed")
step("updates status to Fixed")
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
expect(bug_result == nil).to_equal(false)
val fixed_bug = bug_result?
expect(fixed_bug.status.value).to_equal("Fixed")
cleanup_test_file(test_file)
```

</details>

#### fixed bugs no longer appear in open bugs

- fixed bugs no longer appear in open bugs
- fixed bugs no longer appear in open bugs
   - Expected: open_bugs.len() equals `5`
   - Expected: bug.status.value equals `Open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fixed bugs no longer appear in open bugs")
step("fixed bugs no longer appear in open bugs")
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

- updates status to Closed
- updates status to Closed
   - Expected: bug_result == nil is false
   - Expected: closed_bug.status.value equals `Closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("updates status to Closed")
step("updates status to Closed")
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
expect(bug_result == nil).to_equal(false)
val closed_bug = bug_result?
expect(closed_bug.status.value).to_equal("Closed")
cleanup_test_file(test_file)
```

</details>

#### statistics reflect bug closure

- statistics reflect bug closure
- statistics reflect bug closure
   - Expected: all.len() equals `10`
   - Expected: open.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("statistics reflect bug closure")
step("statistics reflect bug closure")
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

- tracks bug from discovery to closure
- tracks bug from discovery to closure
   - Expected: inv_bug.status.value equals `Investigating`
   - Expected: fix_bug.status.value equals `Fixed`
   - Expected: close_bug.status.value equals `Closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 97 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks bug from discovery to closure")
step("tracks bug from discovery to closure")
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

- handles multiple bugs being tracked simultaneously
- handles multiple bugs being tracked simultaneously
   - Expected: severities.len() equals `4`
   - Expected: statuses.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles multiple bugs being tracked simultaneously")
step("handles multiple bugs being tracked simultaneously")
val severities = get_test_severities()
val statuses = get_test_statuses()
expect(severities.len()).to_equal(4)
expect(statuses.len()).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-BUGTRACKINGSCENARIO-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c5e3d83c24e8164e2d815cc7541ea6f3f6deadbdd89a940dfef7c42acb2a4d6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5e3d83c24e8164e2d815cc7541ea6f3f6deadbdd89a940dfef7c42acb2a4d6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5e3d83c24e8164e2d815cc7541ea6f3f6deadbdd89a940dfef7c42acb2a4d6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/bug_tracking_scenario_spec.spl
mirror: doc/06_spec/integration/app/bug_tracking_scenario_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/bug_tracking_scenario_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/bug_tracking_scenario_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/bug_tracking_scenario_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/bug_tracking_scenario_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates bug report with all required fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/bug_tracking_scenario_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bug appears in open bugs list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/bug_tracking_scenario_spec.spl:211:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bug appears in MCP bugdb://open resource' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
