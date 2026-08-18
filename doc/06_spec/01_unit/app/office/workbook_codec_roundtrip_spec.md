# workbook_codec_roundtrip_spec

> Formula-preserving workbook codec (lane F4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# workbook_codec_roundtrip_spec

Formula-preserving workbook codec (lane F4).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/workbook_codec_roundtrip_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Formula-preserving workbook codec (lane F4).

`sheet_to_csv` (file_formats.spl) only ever serializes DISPLAY text -- a
formula cell round-trips through CSV as its computed result, not its
expression, so reopening a saved CSV can never re-run the formula. This
proves the alternative native codec (workbook_codec.spl): saving a workbook
with a registered extension function (DOUBLE, the same lane-L3 fixture used
by sheets_function_registry_spec.spl) and a builtin SUM formula, then
reloading and recalculating, reproduces both results AND keeps the original
formula expressions intact in the reloaded model -- not just their cached
display text.

## Scenarios

### Workbook codec (formula-preserving save/reopen)

#### reloads and recalculates DOUBLE (registry function) and SUM (builtin) to the right values

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sheet_function_registry_reset()
assert_true(sheets_ext_register_builtins())
assert_true(sheet_function_registry_has("DOUBLE"))

val workbook = _build_workbook()
val sdn_text = workbook_save(workbook)

match workbook_load(sdn_text):
    case Ok(reloaded):
        val sheet = reloaded.sheets[0]
        expect(cell_display_text(sheet.get_cell("B1"))).to_equal("42")
        expect(cell_display_text(sheet.get_cell("B2"))).to_equal("7")
    case Err(e):
        assert_true(false)
```

</details>

#### preserves the formula EXPRESSION in the reloaded model, not just the display value

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sheet_function_registry_reset()
assert_true(sheets_ext_register_builtins())

val workbook = _build_workbook()
val sdn_text = workbook_save(workbook)

match workbook_decode_sdn(sdn_text):
    case Ok(reloaded):
        val sheet = reloaded.sheets[0]
        match sheet.get_cell("B1").value:
            CellValue.FormulaVal(expr, cached_display):
                expect(expr).to_equal("DOUBLE(A1)")
            _:
                assert_true(false)
        match sheet.get_cell("B2").value:
            CellValue.FormulaVal(expr, cached_display):
                expect(expr).to_equal("SUM(A2:A3)")
            _:
                assert_true(false)
        # A1 is a plain number cell, not a formula.
        match sheet.get_cell("A1").value:
            CellValue.NumberVal(value):
                expect(value).to_equal(21.0)
            _:
                assert_true(false)
    case Err(e):
        assert_true(false)
```

</details>

#### keeps the SDN save deterministic across repeated saves of the same workbook

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sheet_function_registry_reset()
assert_true(sheets_ext_register_builtins())

val workbook = _build_workbook()
val first = workbook_save(workbook)
val second = workbook_save(workbook)

expect(first).to_equal(second)
```

</details>

#### round-trips a sheet name and a plain text cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Notes")
sheet.set_value("C1", "hello world")
val workbook = Workbook(title: "Named", sheets: [sheet], active_sheet: 0)

val sdn_text = workbook_save(workbook)
match workbook_decode_sdn(sdn_text):
    case Ok(reloaded):
        expect(reloaded.sheets[0].name).to_equal("Notes")
        expect(cell_display_text(reloaded.sheets[0].get_cell("C1"))).to_equal("hello world")
    case Err(e):
        assert_true(false)
```

</details>

#### rejects garbage input with Err instead of crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match workbook_decode_sdn("!!! not a workbook at all ###"):
    case Ok(_):
        assert_true(false)
    case Err(err):
        assert_false(err.is_empty())
```

</details>

#### rejects well-formed SDN that is missing the 'sheets' key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match workbook_decode_sdn("{title: \"no sheets here\"}"):
    case Ok(_):
        assert_true(false)
    case Err(_):
        assert_true(true)
```

</details>

#### rejects a sheets array that is present but empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match workbook_decode_sdn("{title: \"empty\", sheets: []}"):
    case Ok(_):
        assert_true(false)
    case Err(_):
        assert_true(true)
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


</details>
