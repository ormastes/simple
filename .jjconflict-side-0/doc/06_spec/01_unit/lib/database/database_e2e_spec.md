# Database E2e Specification

> Tests covering Database E2E.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database E2e Specification

## Scenarios

### Database E2E

#### keeps bug database creation persistence and row conversion available

- keeps bug database creation persistence and row conversion available


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps bug database creation persistence and row conversion available")
val source = bug_database_source()

expect(source).to_contain("fn load_bug_database(path: text) -> BugDatabase?")
expect(source).to_contain("fn create_bug_database(path: text) -> BugDatabase")
expect(source).to_contain("class BugDatabase:")
expect(source).to_contain("fn bug_to_row(bug: Bug) -> SdnRow")
expect(source).to_contain("fn bug_to_row_for_table(bug: Bug, table: SdnTable) -> SdnRow")
expect(source).to_contain("me save() -> bool")
```

</details>

#### keeps end to end bug workflow operations available

- keeps end to end bug workflow operations available


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps end to end bug workflow operations available")
val source = bug_database_source()

expect(source).to_contain("me add_bug(bug: Bug) -> bool")
expect(source).to_contain("fn get_bug(id: text) -> Bug?")
expect(source).to_contain("fn all_bugs() -> [Bug]")
expect(source).to_contain("me update_bug(id: text, bug: Bug) -> bool")
expect(source).to_contain("me resolve_bug(id: text, timestamp: text) -> bool")
expect(source).to_contain("fn bugs_by_status(status: BugStatus) -> [Bug]")
expect(source).to_contain("fn bugs_by_severity(severity: BugSeverity) -> [Bug]")
```

</details>

#### keeps bug database validation and status mapping available

- keeps bug database validation and status mapping available


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps bug database validation and status mapping available")
val source = bug_database_source()

expect(source).to_contain("fn validate_test_links() -> [text]")
expect(source).to_contain("fn validate_fix_strategy() -> [text]")
expect(source).to_contain("fn validate() -> [DbIssue]")
expect(source).to_contain("fn severity_to_string(severity: BugSeverity) -> text")
expect(source).to_contain("fn status_to_storage_string(status: BugStatus) -> text")
expect(source).to_contain("fn parse_status(s: text) -> BugStatus")
expect(source).to_contain("\"documented_limitation\": BugStatus.Closed")
```

</details>

#### keeps database persistence backed by SDN and atomic writes

- keeps database persistence backed by SDN and atomic writes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps database persistence backed by SDN and atomic writes")
val core = core_database_source()
val atomic = atomic_database_source()

expect(core).to_contain("class SdnDatabase:")
expect(core).to_contain("static fn load(path: text) -> SdnDatabase?")
expect(core).to_contain("me save() -> bool")
expect(core).to_contain("crc32_text(body)")
expect(core).to_contain("atomic_write(self.path, content)")
expect(atomic).to_contain("fn atomic_write(path: text, content: text) -> bool")
expect(atomic).to_contain("fn atomic_read(path: text) -> text?")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/database_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Database E2E.
- Database E2E

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `19ce107f4f68922b7c7912963ce2eabdf82ab124868d1151809a5ba7d6ce6faa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19ce107f4f68922b7c7912963ce2eabdf82ab124868d1151809a5ba7d6ce6faa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19ce107f4f68922b7c7912963ce2eabdf82ab124868d1151809a5ba7d6ce6faa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/database/database_e2e_spec.spl
mirror: doc/06_spec/01_unit/lib/database/database_e2e_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/database/database_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/database/database_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/database/database_e2e_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps bug database creation persistence and row conversion available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/database_e2e_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps end to end bug workflow operations available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/database_e2e_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps bug database validation and status mapping available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
