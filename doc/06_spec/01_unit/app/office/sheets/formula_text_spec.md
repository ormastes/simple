# formula_text_spec

> Calc text functions spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_text_spec

Calc text functions spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_text_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc text functions spec.

CONCAT/UPPER/LOWER/TRIM/LEN/LEFT/RIGHT/MID/EXACT over cell refs and string
literals. Text cells keep their text (no numeric coercion); MID is 1-based;
out-of-range counts clamp.

## Scenarios

### Calc text functions

#### CONCAT joins refs and string literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CONCAT(A1, \" \", A2)")).to_equal("hello World")
```

</details>

#### UPPER/LOWER/TRIM transform case and whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=UPPER(A1)")).to_equal("HELLO")
expect(_eval("=LOWER(A2)")).to_equal("world")
expect(_eval("=TRIM(\"  x  \")")).to_equal("x")
```

</details>

#### LEN counts characters of a text cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LEN(A1)")).to_equal("5")
```

</details>

#### LEFT/RIGHT/MID slice with 1-based MID and clamped counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LEFT(A2, 3)")).to_equal("Wor")
expect(_eval("=RIGHT(A2, 2)")).to_equal("ld")
expect(_eval("=MID(A2, 2, 3)")).to_equal("orl")
expect(_eval("=LEFT(A2, 99)")).to_equal("World")
```

</details>

#### EXACT compares case-sensitively

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=EXACT(A1, \"hello\")")).to_equal("TRUE")
expect(_eval("=EXACT(A1, \"Hello\")")).to_equal("FALSE")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
