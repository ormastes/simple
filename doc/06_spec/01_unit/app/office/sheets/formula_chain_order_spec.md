# formula_chain_order_spec

> Calc recalculation evaluates formula cells in dependency order.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_chain_order_spec

Calc recalculation evaluates formula cells in dependency order.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_chain_order_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc recalculation evaluates formula cells in dependency order.

`file_formats._ff_dep_plan` already built the reference graph for circular
detection; the peel order it produces is a topological order, and
`recalculate_formula_cells` now evaluates the acyclic cells in it, parking each
numeric result in the sheet as a plain number for the rest of the pass.

That is a CORRECTNESS fix, not only a speed-up. `formula._resolve_cell_value`
resolves a referenced formula by re-evaluating its expression, bounded by
`MAX_EVAL_DEPTH = 64` — two frames per hop — so before this change a chain
longer than ~33 hops silently returned 0.0 at the bound and cached a plausible
but WRONG number. Measured on a 60-cell `A1=1, An = A(n-1)+1` chain, one
`recalculate_formula_cells` call:

    before: A33 = 33, A34 = 33, A40 = 33, A60 = 33   (27 of 59 cells wrong)
    after:  A33 = 33, A34 = 34, A40 = 40, A60 = 60   (0 wrong), 37.07s -> 6.29s

Ground truth is trivial arithmetic: cell n of the chain holds n.

## Scenarios

### Calc recalculation: dependency-ordered evaluation

#### a three-hop chain is correct after a single recalculate call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _reverse_chain()
expect(_disp(sh, "C1")).to_equal("8")
expect(_disp(sh, "D1")).to_equal("16")
```

</details>

#### a chain shorter than the old recursion bound is unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _chain(60)
expect(_disp(sh, "A2")).to_equal("2")
expect(_disp(sh, "A33")).to_equal("33")
```

</details>

#### a chain PAST the old recursion bound no longer caps at 33

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _chain(60)
expect(_disp(sh, "A34")).to_equal("34")
expect(_disp(sh, "A40")).to_equal("40")
expect(_disp(sh, "A60")).to_equal("60")
```

</details>

#### every cell of a 60-long chain holds its own index

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _chain(60)
var wrong = 0
var i = 2
while i <= 60:
    if _disp(sh, "A{i}") != "{i}":
        wrong = wrong + 1
    i = i + 1
expect(wrong).to_equal(0)
```

</details>

#### recalculating a deep chain twice keeps the same displays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _chain(60)
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A60")).to_equal("60")
```

</details>

#### cells stay formulas after the pass — parked numbers are restored

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If Phase 3 failed to restore a parked cell, A6 would be a frozen
# literal and editing the head of the chain could not move it.
var sh = _chain(6)
sh.set_value("A1", "10")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A6")).to_equal("15")
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
