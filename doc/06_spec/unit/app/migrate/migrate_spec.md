# Migrate Specification

> Tests covering Migration Types, Migration Plan, Migration Execution, Common Migrations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Migrate Specification

## Scenarios

### Migration Types

#### syntax migration

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- syntax migration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("syntax migration")
val kind = "syntax"
check(kind == "syntax")
```

</details>

#### API migration

- API migration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("API migration")
val kind = "api"
check(kind == "api")
```

</details>

#### import path migration

- import path migration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("import path migration")
val kind = "import"
check(kind == "import")
```

</details>

#### deprecation migration

- deprecation migration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deprecation migration")
val kind = "deprecation"
check(kind == "deprecation")
```

</details>

### Migration Plan

#### plan has steps

- plan has steps


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plan has steps")
val steps = 3
check(steps > 0)
```

</details>

#### plan has dry-run option

- plan has dry-run option


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plan has dry-run option")
val dry_run = true
check(dry_run)
```

</details>

#### plan shows affected files

- plan shows affected files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plan shows affected files")
val files = 10
check(files > 0)
```

</details>

#### plan estimates changes

- plan estimates changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plan estimates changes")
val changes = 50
check(changes > 0)
```

</details>

### Migration Execution

#### backup before migration

- backup before migration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("backup before migration")
val backed_up = true
check(backed_up)
```

</details>

#### apply changes atomically

- apply changes atomically


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("apply changes atomically")
val atomic = true
check(atomic)
```

</details>

#### rollback on failure

- rollback on failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rollback on failure")
val can_rollback = true
check(can_rollback)
```

</details>

#### report results

- report results


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report results")
val migrated = 10
val skipped = 2
val failed = 0
check(migrated > 0)
check(failed == 0)
```

</details>

### Common Migrations

#### rename function

- rename function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rename function")
val old_name = "old_fn"
val new_name = "new_fn"
check(old_name != new_name)
```

</details>

#### change import path

- change import path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("change import path")
val old_path = "std.old_module"
val new_path = "std.new_module"
check(old_path != new_path)
```

</details>

#### update constructor syntax

- update constructor syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("update constructor syntax")
val old_syntax = "Type.new()"
val new_syntax = "Type()"
check(old_syntax != new_syntax)
```

</details>

#### add type annotation

- add type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add type annotation")
val before = "val x = 42"
val after = "val x: i64 = 42"
check(after.contains("i64"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/migrate/migrate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Migration Types, Migration Plan, Migration Execution, Common Migrations.
- Migration Types
- Migration Plan
- Migration Execution
- Common Migrations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `49a900b1006db5a28d8788cf970ef186fda8a8b8c254ad04b86355cbdff8b7cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `49a900b1006db5a28d8788cf970ef186fda8a8b8c254ad04b86355cbdff8b7cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `49a900b1006db5a28d8788cf970ef186fda8a8b8c254ad04b86355cbdff8b7cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/migrate/migrate_spec.spl
mirror: doc/06_spec/unit/app/migrate/migrate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/migrate/migrate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/migrate/migrate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/migrate/migrate_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'syntax migration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/migrate/migrate_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'API migration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/migrate/migrate_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'import path migration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
