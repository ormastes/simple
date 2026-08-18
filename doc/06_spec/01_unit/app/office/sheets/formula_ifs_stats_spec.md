# formula_ifs_stats_spec

> Calc plural-criteria + statistics-tail functions spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_ifs_stats_spec

Calc plural-criteria + statistics-tail functions spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_ifs_stats_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc plural-criteria + statistics-tail functions spec.

Plural criteria (multi-range AND semantics, Excel argument order): SUMIFS
puts the value range FIRST, followed by (crit_range, criteria) pairs, unlike
singular SUMIF; COUNTIFS/AVERAGEIFS/MAXIFS/MINIFS follow the same shape. A row
qualifies only when every (crit_range[i], criteria) pair matches, and all
ranges must be congruent else #ERR.

Statistics tail: QUARTILE (inclusive linear interpolation, pos = q/4*(n-1)),
PERCENTRANK (inclusive, 3 significant digits), TRIMMEAN (trim FLOOR(n*p/2) from
each end), SKEW / KURT (Excel sample formulas), COUNTBLANK / COUNTA over cell
ranges. Fractional expectations verified against recomputed Excel values.

## Scenarios

### Calc plural-criteria aggregation

#### SUMIFS sums the value range where all criteria match (value range first)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SUMIFS(A1:A4, B1:B4, \"x\")")).to_equal("20")
expect(_eval("=SUMIFS(A1:A4, B1:B4, \"x\", C1:C4, \">1\")")).to_equal("15")
```

</details>

#### COUNTIFS counts rows matching every criteria pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=COUNTIFS(B1:B4, \"y\", A1:A4, \">=10\")")).to_equal("2")
expect(_eval("=COUNTIFS(B1:B4, \"x\")")).to_equal("2")
```

</details>

#### AVERAGEIFS averages qualifying value cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=AVERAGEIFS(A1:A4, B1:B4, \"y\")")).to_equal("15")
```

</details>

#### MAXIFS and MINIFS reduce qualifying value cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=MAXIFS(A1:A4, C1:C4, \"<4\")")).to_equal("15")
expect(_eval("=MINIFS(A1:A4, B1:B4, \"y\")")).to_equal("10")
```

</details>

#### incongruent ranges fail closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SUMIFS(A1:A4, B1:B2, \"x\")")).to_contain("#ERR")
expect(_eval("=COUNTIFS(B1:B4, \"x\", A1:A2, \">1\")")).to_contain("#ERR")
```

</details>

### Calc statistics tail

#### QUARTILE interpolates via q/4*(n-1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=QUARTILE(D1:D4, 1)")).to_start_with("1.75")
expect(_eval("=QUARTILE(D1:D4, 2)")).to_start_with("2.5")
expect(_eval("=QUARTILE(E1:E5, 3)")).to_equal("3")
```

</details>

#### QUARTILE q=5 is out of domain

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=QUARTILE(D1:D4, 5)")).to_contain("#ERR")
```

</details>

#### PERCENTRANK is inclusive to 3 significant digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=PERCENTRANK(F1:F5, 3)")).to_start_with("0.5")
expect(_eval("=PERCENTRANK(F1:F5, 4)")).to_start_with("0.75")
```

</details>

#### TRIMMEAN trims FLOOR(n*p/2) from each end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TRIMMEAN(G1:G10, 0.2)")).to_start_with("5.5")
```

</details>

#### TRIMMEAN percent >= 1 fails closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TRIMMEAN(G1:G10, 1)")).to_contain("#ERR")
```

</details>

#### SKEW and KURT match Excel sample formulas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SKEW(H1:H10)")).to_start_with("0.35954")
expect(_eval("=KURT(H1:H10)")).to_start_with("-0.1517")
```

</details>

#### COUNTA counts non-empty and COUNTBLANK counts empty cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=COUNTA(A1:A4)")).to_equal("4")
expect(_eval("=COUNTA(I1:I4)")).to_equal("2")
expect(_eval("=COUNTBLANK(I1:I4)")).to_equal("2")
expect(_eval("=COUNTBLANK(A1:A4)")).to_equal("0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
