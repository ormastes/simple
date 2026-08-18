# sheet_gui_fmt_spec

> Sheet GUI number-format display + data-validation editing spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sheet_gui_fmt_spec

Sheet GUI number-format display + data-validation editing spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheet_gui_fmt_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Sheet GUI number-format display + data-validation editing spec.

sheet_gui_view_full(session, rules, formats, max_rows, max_cols) is
sheet_gui_view_with_formats' exact grid (per-cell widgets, selection
bracket, viewport marker, cf "!<marker>" suffixes) with every cell's
display text routed through number_format.spl's cell_display_formatted:
a cell whose FormatSpec carries a num_fmt code renders the FORMATTED
string in the text_dump (and widget text); cells without a format entry
fall back to cell_display_text inside cell_display_formatted itself, so
an empty SheetFormats renders byte-identically to the unformatted views.

session_edit_validated / session_key_validated enforce validation.spl's
rules at COMMIT time, Excel-style: invalid input leaves the session
unchanged (cell keeps its value, re-render dumps byte-identically) and
the returned SheetEditOutcome.last_error carries the rule's message;
valid input commits exactly like session_edit/session_key.

Hand-verified format ground truth (same values as number_format_spec):
- format_number(1234.5, "$#,##0.00") = "$1,234.50"
- format_number(42.0,   "$#,##0.00") = "$42.00"
- format_number(0.4567, "0.0%")      = "45.7%"
- format_number(45107.0, "yyyy-mm-dd") = "2023-06-30" (Excel date serial)

Dump line layout (from the session-view functions): lines[0] is the
"viewport|..." marker, lines[1] the column-letter header, lines[2..] one
line per visible row ("<rownum>|<cell>|<cell>...").

## Scenarios

### sheet_gui_view_full: formatted display

#### renders a currency-formatted cell as its formatted string ($#,##0.00)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Money")
sheet.set_value("A1", "1234.5")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "A1", "$#,##0.00")
val session = session_new(sheet, "")
val no_rules: [CondRule] = []
val view = sheet_gui_view_full(session, no_rules, formats, 1, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|$1,234.50")
```

</details>

#### renders a percent-formatted cell (0.4567 with 0.0% -> 45.7%)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Pct")
sheet.set_value("A1", "0.4567")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "A1", "0.0%")
val session = session_new(sheet, "")
val no_rules: [CondRule] = []
val view = sheet_gui_view_full(session, no_rules, formats, 1, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|45.7%")
```

</details>

#### renders a date-code cell from an Excel serial (45107 -> 2023-06-30)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Dates")
sheet.set_value("A1", "45107")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "A1", "yyyy-mm-dd")
val session = session_new(sheet, "")
val no_rules: [CondRule] = []
val view = sheet_gui_view_full(session, no_rules, formats, 1, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|2023-06-30")
```

</details>

#### renders byte-identically to sheet_gui_view_with_selection with an empty format container

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
val session = session_new(sheet, "B2")
val no_rules: [CondRule] = []
val formats = empty_sheet_formats()
val full_view = sheet_gui_view_full(session, no_rules, formats, 3, 2)
val plain_view = sheet_gui_view_with_selection(session, 3, 2)
expect(full_view.text_dump).to_equal(plain_view.text_dump)
```

</details>

#### renders byte-identically to sheet_gui_view_with_formats with an empty format container (cf rules active)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "B2:B3", kind: "above_average", criteria: "", n: 0, css: "")]
val formats = empty_sheet_formats()
val full_view = sheet_gui_view_full(session, rules, formats, 3, 2)
val cf_view = sheet_gui_view_with_formats(session, rules, 3, 2)
expect(full_view.text_dump).to_equal(cf_view.text_dump)
```

</details>

#### leaves every unformatted cell's dump line identical when only one cell has a format

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
val session = session_new(sheet, "")
val no_rules: [CondRule] = []
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "B3", "$#,##0.00")
val full_view = sheet_gui_view_full(session, no_rules, formats, 3, 2)
val plain_view = sheet_gui_view_with_selection(session, 3, 2)
val full_lines = full_view.text_dump.split("\n")
val plain_lines = plain_view.text_dump.split("\n")
expect(full_lines[0]).to_equal(plain_lines[0])
expect(full_lines[1]).to_equal(plain_lines[1])
expect(full_lines[2]).to_equal(plain_lines[2])
expect(full_lines[3]).to_equal(plain_lines[3])
expect(full_lines[4]).to_equal("3|Gadget|$1,234.50")
```

</details>

#### formats a formula cell's numeric result (=A1+A2 -> $42.00)

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Formulas")
sheet.set_value("A1", "10")
sheet.set_value("A2", "32")
sheet.set_value("A3", "=A1+A2")
sheet = recalculate_formula_cells(sheet)
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "A3", "$#,##0.00")
val session = session_new(sheet, "")
val no_rules: [CondRule] = []
val view = sheet_gui_view_full(session, no_rules, formats, 3, 1)
val lines = view.text_dump.split("\n")
expect(lines[4]).to_equal("3|$42.00")
```

</details>

#### wraps the selection bracket around the FORMATTED text

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("SelFmt")
sheet.set_value("A1", "1234.5")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "A1", "$#,##0.00")
val session = session_new(sheet, "A1")
val no_rules: [CondRule] = []
val view = sheet_gui_view_full(session, no_rules, formats, 1, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|[$1,234.50]")
```

</details>

### session_edit_validated: validation-enforced editing

#### commits a valid edit and the grid re-renders it formatted

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "B2", "$#,##0.00")
var vrules = empty_validation_rules()
vrules = validation_add(vrules, "B", "whole_number", "", 1.0, 100.0, "", "Price must be a whole number between 1 and 100")
val session = session_new(sheet, "")
val outcome = session_edit_validated(session, "B2", "42", vrules)
expect(outcome.last_error).to_equal("")
val no_rules: [CondRule] = []
val view = sheet_gui_view_full(outcome.session, no_rules, formats, 3, 2)
val lines = view.text_dump.split("\n")
expect(lines[3]).to_equal("2|Widget|$42.00")
```

</details>

#### rejects an out-of-range value with the rule's message and an unchanged dump

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
var vrules = empty_validation_rules()
vrules = validation_add(vrules, "B", "whole_number", "", 1.0, 100.0, "", "Price must be a whole number between 1 and 100")
val session = session_new(sheet, "")
val no_rules: [CondRule] = []
val formats = empty_sheet_formats()
val before_view = sheet_gui_view_full(session, no_rules, formats, 3, 2)
val outcome = session_edit_validated(session, "B2", "999", vrules)
expect(outcome.last_error).to_equal("Price must be a whole number between 1 and 100")
val after_view = sheet_gui_view_full(outcome.session, no_rules, formats, 3, 2)
expect(after_view.text_dump).to_equal(before_view.text_dump)
```

</details>

#### rejects a non-integer for a whole_number rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
var vrules = empty_validation_rules()
vrules = validation_add(vrules, "B", "whole_number", "", 1.0, 100.0, "", "Price must be a whole number between 1 and 100")
val session = session_new(sheet, "")
val outcome = session_edit_validated(session, "B2", "4.5", vrules)
expect(outcome.last_error).to_equal("Price must be a whole number between 1 and 100")
val out_session = outcome.session
val out_sheet = out_session.sheet
val out_cell = out_sheet.get_cell("B2")
expect(cell_display_text(out_cell)).to_equal("10")
```

</details>

#### accepts everything with an empty rules container (matches plain session_edit)

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
val vrules = empty_validation_rules()
val session = session_new(sheet, "")
val outcome = session_edit_validated(session, "B2", "999", vrules)
expect(outcome.last_error).to_equal("")
val plain_session = session_edit(session, "B2", "999")
val no_rules: [CondRule] = []
val formats = empty_sheet_formats()
val validated_view = sheet_gui_view_full(outcome.session, no_rules, formats, 3, 2)
val plain_view = sheet_gui_view_full(plain_session, no_rules, formats, 3, 2)
expect(validated_view.text_dump).to_equal(plain_view.text_dump)
```

</details>

#### keeps validation and format working on the SAME cell (valid commit reformats, invalid keeps old formatted value)

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "B2", "$#,##0.00")
var vrules = empty_validation_rules()
vrules = validation_add(vrules, "B2", "whole_number", "", 1.0, 100.0, "", "Price must be a whole number between 1 and 100")
val session = session_new(sheet, "")
val valid_outcome = session_edit_validated(session, "B2", "50", vrules)
expect(valid_outcome.last_error).to_equal("")
val no_rules: [CondRule] = []
val valid_view = sheet_gui_view_full(valid_outcome.session, no_rules, formats, 3, 2)
val valid_lines = valid_view.text_dump.split("\n")
expect(valid_lines[3]).to_equal("2|Widget|$50.00")
val invalid_outcome = session_edit_validated(valid_outcome.session, "B2", "200", vrules)
expect(invalid_outcome.last_error).to_equal("Price must be a whole number between 1 and 100")
val invalid_view = sheet_gui_view_full(invalid_outcome.session, no_rules, formats, 3, 2)
val invalid_lines = invalid_view.text_dump.split("\n")
expect(invalid_lines[3]).to_equal("2|Widget|$50.00")
```

</details>

### session_key_validated: enter-commit validation

#### commits a valid typed buffer on enter

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
var vrules = empty_validation_rules()
vrules = validation_add(vrules, "B", "whole_number", "", 1.0, 100.0, "", "Price must be a whole number between 1 and 100")
var session = session_new(sheet, "B2")
session = session_key(session, "4", 3, 2, 3, 2)
session = session_key(session, "2", 3, 2, 3, 2)
val outcome = session_key_validated(session, "enter", 3, 2, 3, 2, vrules)
expect(outcome.last_error).to_equal("")
val out_session = outcome.session
expect(out_session.pending_input).to_equal("")
val out_sheet = out_session.sheet
val out_cell = out_sheet.get_cell("B2")
expect(cell_display_text(out_cell)).to_equal("42")
```

</details>

#### rejects an invalid typed buffer on enter, retaining the buffer and the mid-typing dump

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
var vrules = empty_validation_rules()
vrules = validation_add(vrules, "B", "whole_number", "", 1.0, 100.0, "", "Price must be a whole number between 1 and 100")
var session = session_new(sheet, "B2")
session = session_key(session, "9", 3, 2, 3, 2)
session = session_key(session, "9", 3, 2, 3, 2)
session = session_key(session, "9", 3, 2, 3, 2)
val no_rules: [CondRule] = []
val formats = empty_sheet_formats()
val before_view = sheet_gui_view_full(session, no_rules, formats, 3, 2)
val outcome = session_key_validated(session, "enter", 3, 2, 3, 2, vrules)
expect(outcome.last_error).to_equal("Price must be a whole number between 1 and 100")
val out_session = outcome.session
expect(out_session.pending_input).to_equal("999")
val out_sheet = out_session.sheet
val out_cell = out_sheet.get_cell("B2")
expect(cell_display_text(out_cell)).to_equal("10")
val after_view = sheet_gui_view_full(out_session, no_rules, formats, 3, 2)
expect(after_view.text_dump).to_equal(before_view.text_dump)
```

</details>

#### passes non-commit keys through untouched (arrow move, no validation)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _price_sheet()
var vrules = empty_validation_rules()
vrules = validation_add(vrules, "B", "whole_number", "", 1.0, 100.0, "", "Price must be a whole number between 1 and 100")
val session = session_new(sheet, "B2")
val outcome = session_key_validated(session, "down", 3, 2, 3, 2, vrules)
expect(outcome.last_error).to_equal("")
val out_session = outcome.session
expect(out_session.selected_ref).to_equal("B3")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
