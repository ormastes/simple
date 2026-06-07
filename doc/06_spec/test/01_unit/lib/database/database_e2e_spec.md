# Database E2e Specification

> <details>

<!-- sdn-diagram:id=database_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_e2e_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database E2e Specification

## Scenarios

### Database E2E

#### keeps bug database creation persistence and row conversion available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val core = core_database_source()
val atomic = atomic_database_source()

expect(core).to_contain("class SdnDatabase:")
expect(core).to_contain("static fn load(path: text) -> SdnDatabase?")
expect(core).to_contain("me save() -> bool")
expect(core).to_contain("rt_crc32_text(body)")
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
