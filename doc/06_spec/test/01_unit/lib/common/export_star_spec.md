# Export Star Specification

> Tests that `export *` is parsed into `Stmt.ExportUseStmt("", ImportTarget.Glob)`, and that `export foo, bar` still produces `Stmt.Export(["foo","bar"])`.

<!-- sdn-diagram:id=export_star_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=export_star_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

export_star_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=export_star_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export Star Specification

Tests that `export *` is parsed into `Stmt.ExportUseStmt("", ImportTarget.Glob)`, and that `export foo, bar` still produces `Stmt.Export(["foo","bar"])`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TODO-26 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/common/export_star_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that `export *` is parsed into `Stmt.ExportUseStmt("", ImportTarget.Glob)`,
and that `export foo, bar` still produces `Stmt.Export(["foo","bar"])`.

## Scenarios

### export * parsing

#### parses export star into ExportUseStmt with Glob target

1. fail
2. fail
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_stmt("export *")
match result:
    case Ok(stmt):
        match stmt:
            case Stmt.ExportUseStmt(path, target):
                expect(path).to_equal("")
                match target:
                    case ImportTarget.Glob:
                        expect(target).to_equal(ImportTarget.Glob)
                    case _:
                        fail("unexpected export parser result shape")
            case _:
                fail("unexpected export parser result shape")
    case Err(e):
        fail("unexpected export parser result shape")
```

</details>

#### parses export name list into Stmt.Export

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_stmt("export foo, bar")
match result:
    case Ok(stmt):
        match stmt:
            case Stmt.Export(names):
                expect(names.len()).to_equal(2)
                expect(names[0]).to_equal("foo")
                expect(names[1]).to_equal("bar")
            case _:
                fail("unexpected export parser result shape")
    case Err(e):
        fail("unexpected export parser result shape")
```

</details>

#### parses export single name into Stmt.Export

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_stmt("export baz")
match result:
    case Ok(stmt):
        match stmt:
            case Stmt.Export(names):
                expect(names.len()).to_equal(1)
                expect(names[0]).to_equal("baz")
            case _:
                fail("unexpected export parser result shape")
    case Err(e):
        fail("unexpected export parser result shape")
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
