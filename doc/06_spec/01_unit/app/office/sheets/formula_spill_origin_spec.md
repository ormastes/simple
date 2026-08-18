# formula_spill_origin_spec

> Spill-origin numeric aggregation spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_spill_origin_spec

Spill-origin numeric aggregation spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_spill_origin_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Spill-origin numeric aggregation spec.

Regression spec for doc/08_tracking/bug/
formula_spill_origin_drop_in_numeric_path_2026-07-04.md: the origin cell of a
dynamic-array spill stays a FormulaVal, and `_resolve_cell_value` used to
re-evaluate it through the SCALAR path — where array-registered functions
(SEQUENCE/MMULT/...) have no handler — so the origin contributed 0 to
SUM/AVERAGE over its own spill range (=SUM over a SEQUENCE(2,2) spill gave 9,
not 10). The fix prefers the numeric parse of `cached_display` for FormulaVal
cells whose expression evaluate_formula_array recognizes (non-empty grid).

Ground truth (hand-computed):
- SEQUENCE(2,2) spills 1 2 / 3 4 → SUM 10, AVERAGE 2.5.
- MMULT(A1:B2,A1:B2) on the fixture A1=10 A2=20 B1=30 B2=40, i.e. rows
  [10,30],[20,40]: [[10*10+30*20, 10*30+30*40],[20*10+40*20, 20*30+40*40]]
  = [[700,1500],[1000,2200]] → SUM 5400.
- OFFSET(A1,0,0,2,2) spills 10 30 / 20 40 → SUM 100 (OFFSET is on BOTH the
  scalar and array paths; its cached origin display equals the scalar
  top-left, so the total must stay 100 after the fix).
- A plain scalar formula origin (=1+1) in a summed range contributes 2 —
  the non-array path is unchanged.

## Scenarios

### spill-origin cell in numeric aggregation

#### SUM over a SEQUENCE(2,2) spill totals 10 (origin contributes 1, not 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_spill_then("=SEQUENCE(2,2)", "=SUM(D1:E2)")).to_equal("10")
```

</details>

#### AVERAGE over a SEQUENCE(2,2) spill is 2.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_spill_then("=SEQUENCE(2,2)", "=AVERAGE(D1:E2)")).to_equal("2.5")
```

</details>

#### SUM over an MMULT(A1:B2,A1:B2) spill totals 5400 (700+1500+1000+2200)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_spill_then("=MMULT(A1:B2,A1:B2)", "=SUM(D1:E2)")).to_equal("5400")
```

</details>

#### SUM over an OFFSET(A1,0,0,2,2) spill still totals 100 (dual-path fn)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_spill_then("=OFFSET(A1,0,0,2,2)", "=SUM(D1:E2)")).to_equal("100")
```

</details>

#### OFFSET spill origin display equals the scalar top-left (both sources agree)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=OFFSET(A1,0,0,2,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("10")
```

</details>

#### a plain scalar formula origin (=1+1) still contributes 2 to SUM

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "3")
sh.set_value("B1", "4")
sh.set_value("C1", "=1+1")
sh = recalculate_formula_cells(sh)
sh.set_value("G1", "=SUM(A1:C1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "G1")).to_equal("9")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
