# Basic Type Checker Integration Tests

> This spec exercises a tiny parser-safe type-checker harness so the file stays

<!-- sdn-diagram:id=type_checker_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_checker_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_checker_basic_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_checker_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Type Checker Integration Tests

This spec exercises a tiny parser-safe type-checker harness so the file stays

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/type_checker/type_checker_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

This spec exercises a tiny parser-safe type-checker harness so the file stays
executable without relying on the unsupported BDD syntax from the original
extraction.

## Scenarios

### Type Checker Integration

#### Type checker validates correct code

1. checker declare
2. checker declare
   - Expected: checker.assign("count", TypeKind.Int) is true
   - Expected: checker.check_return(TypeKind.Int, TypeKind.Int) is true
   - Expected: checker.error_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeCheckerHarness.new()
checker.declare("count", TypeKind.Int)
checker.declare("flag", TypeKind.Bool)
expect(checker.assign("count", TypeKind.Int)).to_equal(true)
expect(checker.check_return(TypeKind.Int, TypeKind.Int)).to_equal(true)
expect(checker.error_count()).to_equal(0)
```

</details>

#### Type checker catches type errors

1. checker declare
   - Expected: checker.assign("count", TypeKind.Bool) is false
   - Expected: checker.error_count() equals `1`
   - Expected: checker.has_error("type mismatch for count") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeCheckerHarness.new()
checker.declare("count", TypeKind.Int)
expect(checker.assign("count", TypeKind.Bool)).to_equal(false)
expect(checker.error_count()).to_equal(1)
expect(checker.has_error("type mismatch for count")).to_equal(true)
```

</details>

#### Type checker rejects undeclared variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeCheckerHarness.new()
expect(checker.assign("missing", TypeKind.Text)).to_equal(false)
expect(checker.error_count()).to_equal(1)
expect(checker.has_error("undeclared variable: missing")).to_equal(true)
```

</details>

#### Type checker catches return mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeCheckerHarness.new()
expect(checker.check_return(TypeKind.Text, TypeKind.Unit)).to_equal(false)
expect(checker.error_count()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
