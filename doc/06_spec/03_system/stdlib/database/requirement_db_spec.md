# Requirement Db Specification

> Tests covering RequirementDatabase creation, RequirementDatabase next_id, RequirementDatabase all_requirements, RequirementDatabase requirements_by_status, RequirementDatabase requirements_by_category, RequirementDatabase descriptions, RequirementDatabase save.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Requirement Db Specification

## Scenarios

### RequirementDatabase creation

#### creates a new database

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a new database
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a new database")
val db_path = "/tmp/test_reqdb_create.sdn"
cleanup(db_path)
var db = RequirementDatabase.create()
expect(1).to_equal(1)
```

</details>

#### adds a requirement and retrieves it

- adds a requirement and retrieves it
   - Expected: retrieved.id equals `REQ-001`
   - Expected: retrieved.title equals `Test requirement`
   - Expected: retrieved.category equals `feature`
   - Expected: retrieved.status equals `draft`
   - Expected: retrieved.priority equals `high`
   - Expected: retrieved.doc_path equals `doc/requirement/req_001.md`
   - Expected: retrieved.plan_path equals `doc/03_plan/plan_001.md`
   - Expected: retrieved.design_path equals `doc/05_design/design_001.md`
   - Expected: retrieved.system_test equals `test/system/req_001_spec.spl`
   - Expected: retrieved.created_at equals `2026-03-14`
   - Expected: retrieved.updated_at equals `2026-03-14`
   - Expected: retrieved.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds a requirement and retrieves it")
val db_path = "/tmp/test_reqdb_add.sdn"
cleanup(db_path)
var db = RequirementDatabase.create()

val req = Requirement(
    id: "REQ-001",
    title: "Test requirement",
    category: "feature",
    status: "draft",
    priority: "high",
    doc_path: "doc/requirement/req_001.md",
    plan_path: "doc/03_plan/plan_001.md",
    design_path: "doc/05_design/design_001.md",
    system_test: "test/system/req_001_spec.spl",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)

db.add_requirement(req)

val retrieved = db.get_requirement("REQ-001")
expect(retrieved.id).to_equal("REQ-001")
expect(retrieved.title).to_equal("Test requirement")
expect(retrieved.category).to_equal("feature")
expect(retrieved.status).to_equal("draft")
expect(retrieved.priority).to_equal("high")
expect(retrieved.doc_path).to_equal("doc/requirement/req_001.md")
expect(retrieved.plan_path).to_equal("doc/03_plan/plan_001.md")
expect(retrieved.design_path).to_equal("doc/05_design/design_001.md")
expect(retrieved.system_test).to_equal("test/system/req_001_spec.spl")
expect(retrieved.created_at).to_equal("2026-03-14")
expect(retrieved.updated_at).to_equal("2026-03-14")
expect(retrieved.valid).to_equal(true)
```

</details>

#### returns empty requirement for unknown ID

- returns empty requirement for unknown ID
   - Expected: retrieved.id equals ``
   - Expected: retrieved.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty requirement for unknown ID")
var db = RequirementDatabase.create()
val retrieved = db.get_requirement("REQ-NONEXISTENT")
expect(retrieved.id).to_equal("")
expect(retrieved.valid).to_equal(false)
```

</details>

### RequirementDatabase next_id

#### generates REQ-001 for empty database

- generates REQ-001 for empty database
   - Expected: id equals `REQ-001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates REQ-001 for empty database")
var db = RequirementDatabase.create()
val id = db.next_id()
expect(id).to_equal("REQ-001")
```

</details>

#### generates sequential IDs

- generates sequential IDs
   - Expected: next equals `REQ-002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates sequential IDs")
var db = RequirementDatabase.create()

val req1 = Requirement(
    id: "REQ-001",
    title: "First requirement",
    category: "feature",
    status: "draft",
    priority: "medium",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
db.add_requirement(req1)

val next = db.next_id()
expect(next).to_equal("REQ-002")
```

</details>

#### generates REQ-003 after two entries

- generates REQ-003 after two entries
   - Expected: next equals `REQ-003`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates REQ-003 after two entries")
var db = RequirementDatabase.create()

val req1 = Requirement(
    id: "REQ-001",
    title: "First",
    category: "feature",
    status: "draft",
    priority: "medium",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
val req2 = Requirement(
    id: "REQ-002",
    title: "Second",
    category: "improvement",
    status: "approved",
    priority: "high",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
db.add_requirement(req1)
db.add_requirement(req2)

val next = db.next_id()
expect(next).to_equal("REQ-003")
```

</details>

### RequirementDatabase all_requirements

#### returns all valid requirements

- returns all valid requirements
   - Expected: all.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns all valid requirements")
var db = RequirementDatabase.create()

val req1 = Requirement(
    id: "REQ-001",
    title: "First",
    category: "feature",
    status: "draft",
    priority: "high",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
val req2 = Requirement(
    id: "REQ-002",
    title: "Second",
    category: "bugfix",
    status: "implemented",
    priority: "medium",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
db.add_requirement(req1)
db.add_requirement(req2)

val all = db.all_requirements()
expect(all.len()).to_equal(2)
```

</details>

### RequirementDatabase requirements_by_status

#### filters requirements by status

- filters requirements by status
   - Expected: drafts.len() equals `1`
   - Expected: drafts[0].id equals `REQ-001`
   - Expected: approved.len() equals `1`
   - Expected: approved[0].id equals `REQ-002`
   - Expected: implemented.len() equals `1`
   - Expected: implemented[0].id equals `REQ-003`
   - Expected: verified.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters requirements by status")
var db = RequirementDatabase.create()

val draft_req = Requirement(
    id: "REQ-001",
    title: "Draft requirement",
    category: "feature",
    status: "draft",
    priority: "high",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
val approved_req = Requirement(
    id: "REQ-002",
    title: "Approved requirement",
    category: "feature",
    status: "approved",
    priority: "medium",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
val impl_req = Requirement(
    id: "REQ-003",
    title: "Implemented requirement",
    category: "bugfix",
    status: "implemented",
    priority: "low",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)

db.add_requirement(draft_req)
db.add_requirement(approved_req)
db.add_requirement(impl_req)

val drafts = db.requirements_by_status("draft")
expect(drafts.len()).to_equal(1)
expect(drafts[0].id).to_equal("REQ-001")

val approved = db.requirements_by_status("approved")
expect(approved.len()).to_equal(1)
expect(approved[0].id).to_equal("REQ-002")

val implemented = db.requirements_by_status("implemented")
expect(implemented.len()).to_equal(1)
expect(implemented[0].id).to_equal("REQ-003")

val verified = db.requirements_by_status("verified")
expect(verified.len()).to_equal(0)
```

</details>

### RequirementDatabase requirements_by_category

#### filters requirements by category

- filters requirements by category
   - Expected: features.len() equals `1`
   - Expected: features[0].id equals `REQ-001`
   - Expected: bugfixes.len() equals `1`
   - Expected: bugfixes[0].id equals `REQ-002`
   - Expected: refactors.len() equals `1`
   - Expected: refactors[0].id equals `REQ-003`
   - Expected: improvements.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters requirements by category")
var db = RequirementDatabase.create()

val feat_req = Requirement(
    id: "REQ-001",
    title: "Feature requirement",
    category: "feature",
    status: "draft",
    priority: "high",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
val bugfix_req = Requirement(
    id: "REQ-002",
    title: "Bugfix requirement",
    category: "bugfix",
    status: "draft",
    priority: "critical",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
val refactor_req = Requirement(
    id: "REQ-003",
    title: "Refactor requirement",
    category: "refactor",
    status: "approved",
    priority: "low",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)

db.add_requirement(feat_req)
db.add_requirement(bugfix_req)
db.add_requirement(refactor_req)

val features = db.requirements_by_category("feature")
expect(features.len()).to_equal(1)
expect(features[0].id).to_equal("REQ-001")

val bugfixes = db.requirements_by_category("bugfix")
expect(bugfixes.len()).to_equal(1)
expect(bugfixes[0].id).to_equal("REQ-002")

val refactors = db.requirements_by_category("refactor")
expect(refactors.len()).to_equal(1)
expect(refactors[0].id).to_equal("REQ-003")

val improvements = db.requirements_by_category("improvement")
expect(improvements.len()).to_equal(0)
```

</details>

### RequirementDatabase descriptions

#### stores and retrieves multiline description

- stores and retrieves multiline description


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores and retrieves multiline description")
var db = RequirementDatabase.create()

val req = Requirement(
    id: "REQ-001",
    title: "Described requirement",
    category: "feature",
    status: "draft",
    priority: "high",
    doc_path: "",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
db.add_requirement(req)

val description = "This is line one.\nThis is line two.\nThis is line three."
db.add_description("REQ-001", description)

val retrieved = db.get_description("REQ-001")
expect(retrieved).to_contain("line one")
expect(retrieved).to_contain("line two")
expect(retrieved).to_contain("line three")
```

</details>

#### returns empty string for unknown req_id

- returns empty string for unknown req_id
   - Expected: desc equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty string for unknown req_id")
var db = RequirementDatabase.create()
val desc = db.get_description("REQ-NONEXISTENT")
expect(desc).to_equal("")
```

</details>

### RequirementDatabase save

#### persists data to disk

- persists data to disk
   - Expected: saved is true
   - Expected: rt_file_exists(db_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("persists data to disk")
val db_path = "/tmp/test_reqdb_save.sdn"
cleanup(db_path)
var db = RequirementDatabase.create()

val req = Requirement(
    id: "REQ-001",
    title: "Persisted requirement",
    category: "feature",
    status: "approved",
    priority: "high",
    doc_path: "doc/requirement/req_001.md",
    plan_path: "",
    design_path: "",
    system_test: "",
    created_at: "2026-03-14",
    updated_at: "2026-03-14",
    valid: true
)
db.add_requirement(req)

val saved = db.save()
expect(saved).to_equal(true)
expect(rt_file_exists(db_path)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/database/requirement_db_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RequirementDatabase creation, RequirementDatabase next_id, RequirementDatabase all_requirements, RequirementDatabase requirements_by_status, RequirementDatabase requirements_by_category, RequirementDatabase descriptions, RequirementDatabase save.
- RequirementDatabase creation
- RequirementDatabase next_id
- RequirementDatabase all_requirements
- RequirementDatabase requirements_by_status
- RequirementDatabase requirements_by_category
- RequirementDatabase descriptions
- RequirementDatabase save

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

- `REQ-SSPEC-SYSTEM`
- `REQ-DB`
- `REQ-001`
- `REQ-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b3cbf0b7ccaafe341841c51603ec7b6a2b42ec8ce3de34efa05df68c95fd84b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3cbf0b7ccaafe341841c51603ec7b6a2b42ec8ce3de34efa05df68c95fd84b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3cbf0b7ccaafe341841c51603ec7b6a2b42ec8ce3de34efa05df68c95fd84b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/stdlib/database/requirement_db_spec.spl
mirror: doc/06_spec/03_system/stdlib/database/requirement_db_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/stdlib/database/requirement_db_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/database/requirement_db_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/database/requirement_db_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/stdlib/database/requirement_db_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/stdlib/database/requirement_db_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a new database' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/database/requirement_db_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds a requirement and retrieves it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/database/requirement_db_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty requirement for unknown ID' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
