# report_spec

> Access-style grouped report spec — report.spl over table.spl + query.spl.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# report_spec

Access-style grouped report spec — report.spl over table.spl + query.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/database/report_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Access-style grouped report spec — report.spl over table.spl + query.spl.

Ground truth is hand-computed against one small sales table:

sales(region, amount):
  East, 100
  East, 200
  West, 300
  West, 400

Sorted ascending by region ("East" < "West" alphabetically), so groups come
out in that order regardless of insertion order.

sum agg:
  East subtotal = 100 + 200 = 300
  West subtotal = 300 + 400 = 700
  grand total   = 300 + 700 = 1000

avg agg (integer division, exact here):
  East subtotal = 300 / 2 = 150
  West subtotal = 700 / 2 = 350
  grand total   = 1000 / 4 = 250

## Scenarios

### report_grouped: sum aggregate

#### renders group headers, detail lines, subtotals, and a grand total

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sales()
val r = report_grouped(t, "region", "amount", "sum")
expect(r).to_contain("== East ==")
expect(r).to_contain("== West ==")
expect(r).to_contain("  East: 100")
expect(r).to_contain("  West: 400")
expect(r).to_contain("  subtotal: 300")
expect(r).to_contain("  subtotal: 700")
expect(r).to_contain("TOTAL: 1000")
```

</details>

#### matches the exact hand-computed report text

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sales()
val r = report_grouped(t, "region", "amount", "sum")
val expected = [
    "== East ==",
    "  East: 100",
    "  East: 200",
    "  subtotal: 300",
    "== West ==",
    "  West: 300",
    "  West: 400",
    "  subtotal: 700",
    "TOTAL: 1000",
].join("\n")
expect(r).to_equal(expected)
```

</details>

### report_grouped: avg aggregate

#### matches the exact hand-computed integer-average report text

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sales()
val r = report_grouped(t, "region", "amount", "avg")
val expected = [
    "== East ==",
    "  East: 100",
    "  East: 200",
    "  subtotal: 150",
    "== West ==",
    "  West: 300",
    "  West: 400",
    "  subtotal: 350",
    "TOTAL: 250",
].join("\n")
expect(r).to_equal(expected)
```

</details>

### report_to_html

#### renders section/h3/subtotal/grand-total markup with escaped detail rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sales()
val h = report_to_html(t, "region", "amount", "sum")
expect(h).to_contain("<section><h3>East</h3><ul>")
expect(h).to_contain("<section><h3>West</h3><ul>")
expect(h).to_contain("<li>East: 100</li>")
expect(h).to_contain("<li>West: 400</li>")
expect(h).to_contain("<p class=\"subtotal\">subtotal: 300</p>")
expect(h).to_contain("<p class=\"subtotal\">subtotal: 700</p>")
expect(h).to_contain("<footer class=\"grand-total\">TOTAL: 1000</footer>")
```

</details>

### tail execution probe

#### confirms the final describe block actually runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 + 1).to_equal(2)
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
