# Calc Cli Specification

> Tests covering standalone Office Calc CLI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Calc Cli Specification

## Scenarios

### standalone Office Calc CLI

#### parses a TUI workbook without requiring the Simple CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_calc_cli(["book.csv", "--tui"])
match parsed:
    case Ok(options):
        expect(options.path).to_equal("book.csv")
        expect(options.tui).to_be(true)
        expect(options.gui).to_be(false)
        expect(options.frame_once).to_be(false)
        expect(options.access_port).to_equal(0)
    case Err(message):
        fail(message)
```

</details>

#### supports a deterministic frame-only SimpleOS launch probe

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_calc_cli(["--frame-once"])
match parsed:
    case Ok(options):
        expect(options.path).to_equal("untitled.csv")
        expect(options.frame_once).to_be(true)
    case Err(message):
        fail(message)
```

</details>

#### rejects unknown options

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_calc_cli(["--not-real"])
match parsed:
    case Ok(_): fail("unknown option was accepted")
    case Err(message): expect(message).to_contain("unknown option")
```

</details>

#### parses validated opt-in UI access for the TUI

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_calc_cli(["book.csv", "--tui", "--ui-access-port", "38123"])
match parsed:
    case Ok(options): expect(options.access_port).to_equal(38123)
    case Err(message): fail(message)
```

</details>

#### parses the browser GUI with a deterministic default or explicit port

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_calc_cli(["book.csv", "--gui"]):
    case Ok(options):
        expect(options.gui).to_be(true)
        expect(options.tui).to_be(false)
        expect(options.access_port).to_equal(3000)
    case Err(message): fail(message)
match parse_calc_cli(["book.csv", "--gui", "--ui-access-port", "38124"]):
    case Ok(options): expect(options.access_port).to_equal(38124)
    case Err(message): fail(message)
```

</details>

#### renders a nonempty Calc GUI from the shared semantic grid tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("gui")
sheet.set_cell("A1", "48")
val html = calc_gui_html(calc_access_controller_with_sheet(sheet))
expect(html).to_contain("Simple Calc")
expect(html).to_contain("formula_input")
expect(html).to_contain("sheet_grid")
expect(html).to_contain("cell_A1")
expect(html).to_contain("48")
```

</details>

#### rejects invalid or frame-only UI access ports

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_calc_cli(["--tui", "--ui-access-port", "0"]):
    case Ok(_): fail("port zero was accepted")
    case Err(message): expect(message).to_contain("between 1 and 65535")
match parse_calc_cli(["--frame-once", "--ui-access-port", "38123"]):
    case Ok(_): fail("frame-only access transport was accepted")
    case Err(message): expect(message).to_contain("requires --tui")
```

</details>

#### renders the fixed 124 by 37 Calc surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = calc_tui_frame(calc_tui_new(Sheet.new("unit")), "unit.csv", false)
val lines = frame.split("\n")
expect(lines.len()).to_equal(37)
expect(lines[0].len()).to_equal(124)
expect(frame).to_contain("Simple Calc")
expect(frame).to_contain("T")
expect(frame).to_contain("30")
```

</details>

#### evaluates multiplication and AVG through real cell commits

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = calc_tui_new(Sheet.new("formula"))
for byte in [54, 13, 56, 13]:
    state = calc_tui_apply_byte(state, byte)
# Move back to A1, then across to B1 and commit multiplication.
state = calc_tui_apply_byte(state, 27)
state = calc_tui_apply_byte(state, 91)
state = calc_tui_apply_byte(state, 65)
state = calc_tui_apply_byte(state, 27)
state = calc_tui_apply_byte(state, 91)
state = calc_tui_apply_byte(state, 65)
state = calc_tui_apply_byte(state, 27)
state = calc_tui_apply_byte(state, 91)
state = calc_tui_apply_byte(state, 67)
for byte in [61, 65, 49, 42, 65, 50, 13]:
    state = calc_tui_apply_byte(state, byte)
state = calc_tui_apply_byte(state, 27)
state = calc_tui_apply_byte(state, 91)
state = calc_tui_apply_byte(state, 65)
state = calc_tui_apply_byte(state, 27)
state = calc_tui_apply_byte(state, 91)
state = calc_tui_apply_byte(state, 67)
for byte in [61, 65, 86, 71, 40, 65, 49, 58, 65, 50, 41, 13]:
    state = calc_tui_apply_byte(state, byte)
expect(cell_display_text(state.sheet.get_cell("B1"))).to_equal("48")
expect(cell_display_text(state.sheet.get_cell("C1"))).to_equal("7")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/calc_cli_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering standalone Office Calc CLI.
- standalone Office Calc CLI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
