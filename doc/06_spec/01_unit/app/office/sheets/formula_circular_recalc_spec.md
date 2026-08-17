# formula_circular_recalc_spec

> Circular-reference detection in the Calc recalculation driver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_circular_recalc_spec

Circular-reference detection in the Calc recalculation driver.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_circular_recalc_spec.spl` |
| Updated | 2026-08-17 |
| Generator | `simple spipe-docgen` (Simple) |

Circular-reference detection in the Calc recalculation driver.

`formula._resolve_cell_value` is depth-bounded, so a circular reference always
TERMINATED — but it terminated by returning 0.0 sixty-four frames down, which
means `A1 = B1+1` / `B1 = A1+1` silently cached the display `33` instead of
reporting the cycle. Measured on the seed before this change:

    A1 display = [33]
    B1 display = [33]

`file_formats.recalculate_formula_cells` now resolves the reference graph up
front (`_ff_circular_cells`, Kahn peeling on outgoing edges) and caches
`#CIRC!` for every formula cell that sits on a cycle or transitively depends on
one, without evaluating it. Non-cyclic chains and ranges are untouched.

Ground truth (hand-computed):
- A1=B1+1, B1=A1+1  -> both `#CIRC!` (mutual cycle).
- H1=H1+1           -> `#CIRC!` (self reference).
- G1=A1+0           -> `#CIRC!` (depends on a cycle without being in one).
- C1=4, D1=C1*2     -> 8; E1=D1+1 -> 9 (a clean two-hop chain still evaluates).
- F1=SUM(C1:D1)     -> 12 (range references are expanded, and a range that
  touches no cycle stays a normal result).

## Scenarios

### Calc recalculation: circular references report #CIRC!

#### a mutually-circular pair reports #CIRC! on both cells, not a number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _mixed_sheet()
expect(_disp(sh, "A1")).to_equal("#CIRC!")
expect(_disp(sh, "B1")).to_equal("#CIRC!")
```

</details>

#### a self-referential formula reports #CIRC!

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_disp(_mixed_sheet(), "H1")).to_equal("#CIRC!")
```

</details>

#### a cell that merely depends on a cycle also reports #CIRC!

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_disp(_mixed_sheet(), "G1")).to_equal("#CIRC!")
```

</details>

#### a clean two-hop chain in the same sheet still evaluates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _mixed_sheet()
expect(_disp(sh, "D1")).to_equal("8")
expect(_disp(sh, "E1")).to_equal("9")
```

</details>

#### a range reference that touches no cycle still evaluates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_disp(_mixed_sheet(), "F1")).to_equal("12")
```

</details>

#### recalculating an already-recalculated sheet keeps the same displays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _mixed_sheet()
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#CIRC!")
expect(_disp(sh, "E1")).to_equal("9")
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
