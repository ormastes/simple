# formula_isomitted_spec

> ISOMITTED function tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_isomitted_spec

ISOMITTED function tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_isomitted_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

ISOMITTED function tests.

## Scenarios

### ISOMITTED basic

#### LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5) = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5)")).to_equal("5")
```

</details>

#### LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5, 3) = 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5, 3)")).to_equal("8")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
