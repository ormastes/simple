# sheets_function_registry_spec

> Sheet function registry (lane L3).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sheets_function_registry_spec

Sheet function registry (lane L3).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets_function_registry_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Sheet function registry (lane L3).

Proves the new function_registry.spl hook in formula.spl: a registered
extension function (the DOUBLE(n) fixture from
src/lib/editor/extensions/builtin/sheets_ext.spl, simulating a third-party
extension) recalculates through the registry, the existing inline dispatch
(SUM) keeps working unchanged as the fallback path, and an unregistered name
still errors exactly as before.

Note: spreadsheet.spl/file_formats.spl have no formula-preserving
save/reopen API (`sheet_to_csv` only serializes DISPLAY text, not formula
expressions) -- see the "recalculates twice deterministically" example below
for the documented fallback the task's gate allows when a real round trip
isn't feasible.

## Scenarios

### Sheet function registry

#### recalculates a registered extension function (DOUBLE) through the registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sheet_function_registry_reset()
assert_true(sheets_ext_register_builtins())
assert_true(sheet_function_registry_has("DOUBLE"))

var sheet = Sheet.new("Registry")
sheet.set_value("A1", "21")
sheet.set_value("B1", "=DOUBLE(A1)")

sheet = recalculate_formula_cells(sheet)

expect(cell_display_text(sheet.get_cell("B1"))).to_equal("42")
```

</details>

#### still resolves builtin SUM through the unchanged inline dispatch (fallback path)

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sheet_function_registry_reset()
assert_false(sheet_function_registry_has("SUM"))

var sheet = Sheet.new("Fallback")
sheet.set_value("A1", "3")
sheet.set_value("A2", "4")
sheet.set_value("B1", "=SUM(A1:A2)")

sheet = recalculate_formula_cells(sheet)

expect(cell_display_text(sheet.get_cell("B1"))).to_equal("7")
```

</details>

#### still errors on an unknown function name exactly as before (no registry match)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sheet_function_registry_reset()

var sheet = Sheet.new("Unknown")
sheet.set_value("A1", "=NOPEFUNCTION(1)")

sheet = recalculate_formula_cells(sheet)

expect(cell_display_text(sheet.get_cell("A1"))).to_equal("#ERR: Unknown function: NOPEFUNCTION")
```

</details>

#### recalculates DOUBLE deterministically across repeated recalcs (save/reopen API gap fallback)

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sheet_function_registry_reset()
assert_true(sheets_ext_register_builtins())

var sheet = Sheet.new("Deterministic")
sheet.set_value("A1", "5")
sheet.set_value("B1", "=DOUBLE(A1)")

sheet = recalculate_formula_cells(sheet)
val first = cell_display_text(sheet.get_cell("B1"))
sheet = recalculate_formula_cells(sheet)
val second = cell_display_text(sheet.get_cell("B1"))

expect(first).to_equal("10")
expect(second).to_equal("10")
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
