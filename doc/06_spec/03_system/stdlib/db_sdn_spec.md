# Database SDN Table Import/Export

> Simple DB supports reading and writing table data as SDN named tables. This spec uses a small local model to validate the parser-safe behavior of importing and exporting SDN tables.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database SDN Table Import/Export

Simple DB supports reading and writing table data as SDN named tables. This spec uses a small local model to validate the parser-safe behavior of importing and exporting SDN tables.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/db_sdn_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple DB supports reading and writing table data as SDN named tables.
This spec uses a small local model to validate the parser-safe behavior of
importing and exporting SDN tables.

## SDN Format
```sdn
users |id, name, active|
    1, "Alice", true
    2, "Bob", false
```

## Scenarios

### Database SDN table import/export

#### exports users table to SDN

- exports users table to SDN


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports users table to SDN")
val table = SdnTable.new("users", ["id", "name", "active"])
var row = SdnTable.empty_row()
row["id"] = "1"
row["name"] = "Alice"
row["active"] = "true"
table.add_row(row)

val exported = table.to_sdn()
expect(exported).to_contain("users |id, name, active|")
expect(exported).to_contain("Alice")
expect(exported).to_contain("true")
```

</details>

#### imports users table from SDN

- imports users table from SDN
   - Expected: resolved.name equals `users`
   - Expected: resolved.columns.len() equals `3`
   - Expected: resolved.rows.len() equals `2`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("imports users table from SDN")
val content = "users |id, name, active|\n    1, \"Alice\", true\n    2, \"Bob\", false"
val table = parse_sdn_table(content)
match table:
    Some(resolved):
        expect(resolved.name).to_equal("users")
        expect(resolved.columns.len()).to_equal(3)
        expect(resolved.rows.len()).to_equal(2)
    nil:
        expect(false).to_equal(true)
```

</details>

#### round-trips quoted values with commas

- round-trips quoted values with commas
   - Expected: resolved.rows.len() equals `1`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("round-trips quoted values with commas")
val table = SdnTable.new("notes", ["id", "description"])
var row = SdnTable.empty_row()
row["id"] = "1"
row["description"] = "hello, world"
table.add_row(row)

val exported = table.to_sdn()
expect(exported).to_contain('"hello, world"')

val parsed = parse_sdn_table(exported)
match parsed:
    Some(resolved):
        expect(resolved.rows.len()).to_equal(1)
    nil:
        expect(false).to_equal(true)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fa031f76fcc6044f0c81838541aea417bd6cdcf19e943229603de94b8bb09689`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa031f76fcc6044f0c81838541aea417bd6cdcf19e943229603de94b8bb09689`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa031f76fcc6044f0c81838541aea417bd6cdcf19e943229603de94b8bb09689`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/stdlib/db_sdn_spec.spl
mirror: doc/06_spec/03_system/stdlib/db_sdn_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/db_sdn_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/db_sdn_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/db_sdn_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/stdlib/db_sdn_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports users table to SDN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/db_sdn_spec.spl:180:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports users table from SDN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/db_sdn_spec.spl:193:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips quoted values with commas' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
