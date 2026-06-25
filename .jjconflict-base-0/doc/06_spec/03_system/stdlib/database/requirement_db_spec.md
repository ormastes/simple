# Requirement Db Specification

> 1. cleanup

<!-- sdn-diagram:id=requirement_db_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=requirement_db_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

requirement_db_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=requirement_db_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Requirement Db Specification

## Scenarios

### RequirementDatabase creation

#### creates a new database

1. cleanup
2. var db = RequirementDatabase create
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/test_reqdb_create.sdn"
cleanup(db_path)
var db = RequirementDatabase.create()
expect(1).to_equal(1)
```

</details>

#### adds a requirement and retrieves it

1. cleanup
2. var db = RequirementDatabase create
3. db add requirement
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

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = RequirementDatabase create
   - Expected: retrieved.id equals ``
   - Expected: retrieved.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = RequirementDatabase.create()
val retrieved = db.get_requirement("REQ-NONEXISTENT")
expect(retrieved.id).to_equal("")
expect(retrieved.valid).to_equal(false)
```

</details>

### RequirementDatabase next_id

#### generates REQ-001 for empty database

1. var db = RequirementDatabase create
   - Expected: id equals `REQ-001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = RequirementDatabase.create()
val id = db.next_id()
expect(id).to_equal("REQ-001")
```

</details>

#### generates sequential IDs

1. var db = RequirementDatabase create
2. db add requirement
   - Expected: next equals `REQ-002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = RequirementDatabase create
2. db add requirement
3. db add requirement
   - Expected: next equals `REQ-003`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = RequirementDatabase create
2. db add requirement
3. db add requirement
   - Expected: all.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = RequirementDatabase create
2. db add requirement
3. db add requirement
4. db add requirement
   - Expected: drafts.len() equals `1`
   - Expected: drafts[0].id equals `REQ-001`
   - Expected: approved.len() equals `1`
   - Expected: approved[0].id equals `REQ-002`
   - Expected: implemented.len() equals `1`
   - Expected: implemented[0].id equals `REQ-003`
   - Expected: verified.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = RequirementDatabase create
2. db add requirement
3. db add requirement
4. db add requirement
   - Expected: features.len() equals `1`
   - Expected: features[0].id equals `REQ-001`
   - Expected: bugfixes.len() equals `1`
   - Expected: bugfixes[0].id equals `REQ-002`
   - Expected: refactors.len() equals `1`
   - Expected: refactors[0].id equals `REQ-003`
   - Expected: improvements.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = RequirementDatabase create
2. db add requirement
3. db add description


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var db = RequirementDatabase create
   - Expected: desc equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = RequirementDatabase.create()
val desc = db.get_description("REQ-NONEXISTENT")
expect(desc).to_equal("")
```

</details>

### RequirementDatabase save

#### persists data to disk

1. cleanup
2. var db = RequirementDatabase create
3. db add requirement
   - Expected: saved is true
   - Expected: rt_file_exists(db_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
