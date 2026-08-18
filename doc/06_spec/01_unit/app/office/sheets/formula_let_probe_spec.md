# formula_let_probe_spec

> Adversarial LET/LAMBDA review probes (coordinator self-review).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_let_probe_spec

Adversarial LET/LAMBDA review probes (coordinator self-review).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_let_probe_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Adversarial LET/LAMBDA review probes (coordinator self-review).

Leak test: a LET that #ERRs must still pop its bindings — a following cell
using the same bare name must #ERR, not resolve to the leaked value.

## Scenarios

### LET adversarial probes

#### does not leak bindings when the LET body #ERRs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("p")
sh.set_value("A1", "=LET(qz, 7, UNKNOWNFN(qz))")
sh.set_value("A2", "=qz")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_contain("#ERR")
expect(_disp(sh, "A2")).to_contain("#ERR")
```

</details>

#### later values can use earlier bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("p")
sh.set_value("B1", "=LET(x, 1, y, x+x, y)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "B1")).to_equal("2")
```

</details>

#### three-level nesting resolves innermost-out

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("p")
sh.set_value("C1", "=LET(a, 1, LET(b, 2, LET(c, 3, a+b+c)))")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "C1")).to_equal("6")
```

</details>

#### LAMBDA params do not leak after invocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("p")
sh.set_value("D1", "=LAMBDA(zq, zq*3)(4)")
sh.set_value("D2", "=zq")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("12")
expect(_disp(sh, "D2")).to_contain("#ERR")
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
