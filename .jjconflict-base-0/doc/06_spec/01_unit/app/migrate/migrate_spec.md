# Migrate Unit Tests

> 1. check

<!-- sdn-diagram:id=migrate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=migrate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

migrate_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=migrate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Migrate Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #APP-MIGRATE-001 |
| Category | App \| Migrate |
| Status | Implemented |
| Source | `test/01_unit/app/migrate/migrate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Migration Types

#### syntax migration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "syntax"
check(kind == "syntax")
```

</details>

#### API migration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "api"
check(kind == "api")
```

</details>

#### import path migration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "import"
check(kind == "import")
```

</details>

#### deprecation migration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "deprecation"
check(kind == "deprecation")
```

</details>

### Migration Plan

#### plan has steps

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val steps = 3
check(steps > 0)
```

</details>

#### plan has dry-run option

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dry_run = true
check(dry_run)
```

</details>

#### plan shows affected files

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = 10
check(files > 0)
```

</details>

#### plan estimates changes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val changes = 50
check(changes > 0)
```

</details>

### Migration Execution

#### backup before migration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backed_up = true
check(backed_up)
```

</details>

#### apply changes atomically

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val atomic = true
check(atomic)
```

</details>

#### rollback on failure

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val can_rollback = true
check(can_rollback)
```

</details>

#### report results

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val migrated = 10
val skipped = 2
val failed = 0
check(migrated > 0)
check(failed == 0)
```

</details>

### Common Migrations

#### rename function

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_name = "old_fn"
val new_name = "new_fn"
check(old_name != new_name)
```

</details>

#### change import path

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_path = "std.old_module"
val new_path = "std.new_module"
check(old_path != new_path)
```

</details>

#### update constructor syntax

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_syntax = "Type.new()"
val new_syntax = "Type()"
check(old_syntax != new_syntax)
```

</details>

#### add type annotation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "val x = 42"
val after = "val x: i64 = 42"
check(after.contains("i64"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
