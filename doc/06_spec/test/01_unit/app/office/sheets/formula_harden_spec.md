# formula_harden_spec

> Verifies hardening of `src/app/office/sheets/formula.spl`: depth-bounded cycle detection and display-safe Calc functions. Circular references terminate with an empty display instead of recursing until the stack overflows.

<!-- sdn-diagram:id=formula_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=formula_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

formula_harden_spec -> std
formula_harden_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=formula_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_harden_spec

Verifies hardening of `src/app/office/sheets/formula.spl`: depth-bounded cycle detection and display-safe Calc functions. Circular references terminate with an empty display instead of recursing until the stack overflows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/calc_formula_display_functions.md |
| Plan | doc/03_plan/sys_test/calc_formula_display_functions.md |
| Design | doc/05_design/app/office/calc_formula_display_functions.md |
| Research | N/A |
| Source | `test/01_unit/app/office/sheets/formula_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies hardening of `src/app/office/sheets/formula.spl`: depth-bounded cycle
detection and display-safe Calc functions. Circular references terminate with
an empty display instead of recursing until the stack overflows.

These examples run on the integer-safe display path
(`evaluate_formula_display_text`) and pass under the test runner's compiled
execution. Display-safe COUNTA, exact-match VLOOKUP, and LEN/LOWER/UPPER/TRIM
are verified here.
The float-returning additions in the same change — ROUND (half away from zero),
SQRT, POWER, MOD, INT, PRODUCT, FLOOR, CEILING, SIGN, the AND/OR/NOT logical
functions, and the '&' string-concatenation operator — are implemented but NOT
yet verified to produce correct values: f64 results are unreliable on every
available backend (interpreter/SMF/runner zero them, native cores, and even
shallow leaf-math calls return garbage bits). They are correct by construction
only. The toolchain blocker — which also makes the pre-existing SUM/AVERAGE
functions return 0 — is tracked in
`doc/08_tracking/bug/interp_f64_nested_struct_payload_zero_2026-06-14.md` and
must be fixed before these functions can be asserted.

## Examples

`=COUNTA(A1:A4,B1,"x","")` counts non-empty display values across ranges and
literal arguments. `=VLOOKUP(D1,A2:B3,2,FALSE)` returns display text from the
matched row. `=lower(A1)` and `=TRIM(A1)` transform cell display text.

**Requirements:** doc/02_requirements/feature/calc_formula_display_functions.md
**NFR:** doc/02_requirements/nfr/calc_formula_display_functions.md
**Plan:** doc/03_plan/sys_test/calc_formula_display_functions.md
**Design:** doc/05_design/app/office/calc_formula_display_functions.md
**Research:** N/A

## Scenarios

### formula engine: cycle detection terminates

#### a self-referential formula returns an empty display instead of overflowing

- var sheet = Sheet new
- sheet set value
   - Expected: evaluate_formula_display_text("=C1", sheet) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("C1", "=C1+1")
expect(evaluate_formula_display_text("=C1", sheet)).to_equal("")
```

</details>

#### mutually-circular references terminate

- var sheet = Sheet new
- sheet set value
- sheet set value
   - Expected: evaluate_formula_display_text("=A1", sheet) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "=B1")
sheet.set_value("B1", "=A1")
expect(evaluate_formula_display_text("=A1", sheet)).to_equal("")
```

</details>

#### an empty formula yields an empty display

- var sheet = Sheet new
   - Expected: evaluate_formula_display_text("=", sheet) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
expect(evaluate_formula_display_text("=", sheet)).to_equal("")
```

</details>

### formula engine: display-safe Calc functions

#### COUNTA counts non-empty cells and literal arguments

- var sheet = Sheet new
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
   - Expected: evaluate_formula_display_text("=COUNTA(A1:A4)", sheet) equals `3`
   - Expected: evaluate_formula_display_text("=COUNTA(A1:A4,B1,\"x\",\"\")", sheet) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Alpha")
sheet.set_value("A2", "")
sheet.set_value("A3", "42")
sheet.set_value("A4", "=LEN(\"xy\")")
sheet.set_value("B1", "FALSE")
expect(evaluate_formula_display_text("=COUNTA(A1:A4)", sheet)).to_equal("3")
expect(evaluate_formula_display_text("=COUNTA(A1:A4,B1,\"x\",\"\")", sheet)).to_equal("5")
```

</details>

#### text functions transform literals and cell display text

- var sheet = Sheet new
- sheet set value
   - Expected: evaluate_formula_display_text("=LEN(\"Office\")", sheet) equals `6`
   - Expected: evaluate_formula_display_text("=lower(A1)", sheet) equals `mixed case`
   - Expected: evaluate_formula_display_text("=UPPER(\"calc\")", sheet) equals `CALC`
   - Expected: evaluate_formula_display_text("=TRIM(A1)", sheet) equals `Mixed Case`
   - Expected: evaluate_formula_display_text("=UNKNOWN(\"x\")", sheet) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "  Mixed Case  ")
expect(evaluate_formula_display_text("=LEN(\"Office\")", sheet)).to_equal("6")
expect(evaluate_formula_display_text("=lower(A1)", sheet)).to_equal("mixed case")
expect(evaluate_formula_display_text("=UPPER(\"calc\")", sheet)).to_equal("CALC")
expect(evaluate_formula_display_text("=TRIM(A1)", sheet)).to_equal("Mixed Case")
expect(evaluate_formula_display_text("=UNKNOWN(\"x\")", sheet)).to_equal("")
```

</details>

#### display functions reject trailing formula tokens

- var sheet = Sheet new
   - Expected: evaluate_formula_display_text("=LEN(\"Office\")+999", sheet) equals ``
   - Expected: evaluate_formula_display_text("=TRIM(\" Office \") & \"x\"", sheet) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
expect(evaluate_formula_display_text("=LEN(\"Office\")+999", sheet)).to_equal("")
expect(evaluate_formula_display_text("=TRIM(\" Office \") & \"x\"", sheet)).to_equal("")
```

</details>

#### VLOOKUP returns exact-match display text and fails closed

- var sheet = Sheet new
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
- sheet set value
   - Expected: evaluate_formula_display_text("=VLOOKUP(\"B-2\",A2:C3,2)", sheet) equals `Nut`
   - Expected: evaluate_formula_display_text("=VLOOKUP(D1,A2:C3,3,FALSE)", sheet) equals `2`
   - Expected: evaluate_formula_display_text("=VLOOKUP(\"missing\",A2:C3,2)", sheet) equals ``
   - Expected: evaluate_formula_display_text("=VLOOKUP(\"A-1\",A2:C3,4)", sheet) equals ``
   - Expected: evaluate_formula_display_text("=VLOOKUP(\"A-1\",A2:C3,2,TRUE)", sheet) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A2", "A-1")
sheet.set_value("B2", "Bolt")
sheet.set_value("C2", "=LEN(\"xx\")")
sheet.set_value("A3", "B-2")
sheet.set_value("B3", "Nut")
sheet.set_value("C3", "9")
sheet.set_value("D1", "A-1")
expect(evaluate_formula_display_text("=VLOOKUP(\"B-2\",A2:C3,2)", sheet)).to_equal("Nut")
expect(evaluate_formula_display_text("=VLOOKUP(D1,A2:C3,3,FALSE)", sheet)).to_equal("2")
expect(evaluate_formula_display_text("=VLOOKUP(\"missing\",A2:C3,2)", sheet)).to_equal("")
expect(evaluate_formula_display_text("=VLOOKUP(\"A-1\",A2:C3,4)", sheet)).to_equal("")
expect(evaluate_formula_display_text("=VLOOKUP(\"A-1\",A2:C3,2,TRUE)", sheet)).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/calc_formula_display_functions.md](doc/02_requirements/feature/calc_formula_display_functions.md)
- **Plan:** [doc/03_plan/sys_test/calc_formula_display_functions.md](doc/03_plan/sys_test/calc_formula_display_functions.md)
- **Design:** [doc/05_design/app/office/calc_formula_display_functions.md](doc/05_design/app/office/calc_formula_display_functions.md)


</details>
