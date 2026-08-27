# Dbfs Dentry Prefix Index Specification

> Tests covering DBFS dentry prefix index.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Dentry Prefix Index Specification

## Scenarios

### DBFS dentry prefix index

#### finds exact children through the shared prefix index

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds exact children through the shared prefix index
   - Expected: found.child_ino equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds exact children through the shared prefix index")
val table = DentryTable.new()
table.insert(DentryRow(parent_ino: 1, name: "src", child_ino: 10, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 2, name: "src", child_ino: 20, gen: 0)).unwrap()

val found = table.find_child_accel(2, "src").unwrap()

expect(found.child_ino).to_equal(20)
```

</details>

#### lists only matching children for the requested parent and prefix

- lists only matching children for the requested parent and prefix
   - Expected: rows.len() equals `2`
   - Expected: rows[0].child_ino equals `1`
   - Expected: rows[1].child_ino equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists only matching children for the requested parent and prefix")
val table = DentryTable.new()
table.insert(DentryRow(parent_ino: 7, name: "src_main", child_ino: 1, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 7, name: "src_test", child_ino: 2, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 7, name: "doc_readme", child_ino: 3, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 8, name: "src_other_parent", child_ino: 4, gen: 0)).unwrap()

val rows = table.list_children_with_prefix(7, "src")

expect(rows.len()).to_equal(2)
expect(rows[0].child_ino).to_equal(1)
expect(rows[1].child_ino).to_equal(2)
```

</details>

#### rebuilds the index after removal so stale row positions are not returned

- rebuilds the index after removal so stale row positions are not returned
   - Expected: rows.len() equals `2`
   - Expected: rows[0].child_ino equals `12`
   - Expected: rows[1].child_ino equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rebuilds the index after removal so stale row positions are not returned")
val table = DentryTable.new()
table.insert(DentryRow(parent_ino: 1, name: "alpha", child_ino: 11, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 1, name: "beta", child_ino: 12, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 1, name: "bravo", child_ino: 13, gen: 0)).unwrap()

table.remove(DentryKey(parent_ino: 1, name: "alpha")).unwrap()
val rows = table.list_children_with_prefix(1, "b")

expect(rows.len()).to_equal(2)
expect(rows[0].child_ino).to_equal(12)
expect(rows[1].child_ino).to_equal(13)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/db/dbfs_dentry_prefix_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DBFS dentry prefix index.
- DBFS dentry prefix index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6a54be1c6367ca79ea473dab82c14df12a2de7807d3061575f1b495c581a3aa3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a54be1c6367ca79ea473dab82c14df12a2de7807d3061575f1b495c581a3aa3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a54be1c6367ca79ea473dab82c14df12a2de7807d3061575f1b495c581a3aa3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/db/dbfs_dentry_prefix_index_spec.spl
mirror: doc/06_spec/unit/lib/db/dbfs_dentry_prefix_index_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/db/dbfs_dentry_prefix_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/db/dbfs_dentry_prefix_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/db/dbfs_dentry_prefix_index_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/db/dbfs_dentry_prefix_index_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds exact children through the shared prefix index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/db/dbfs_dentry_prefix_index_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists only matching children for the requested parent and prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/db/dbfs_dentry_prefix_index_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rebuilds the index after removal so stale row positions are not returned' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
