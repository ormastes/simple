# sheet_gui_cf_spec

> Sheet GUI conditional formatting spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sheet_gui_cf_spec

Sheet GUI conditional formatting spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheet_gui_cf_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Sheet GUI conditional formatting spec.

sheet_gui_view_with_formats(session, rules, max_rows, max_cols) renders the
same grid as sheet_gui_view_with_selection but consults the cond_format
engine's rules per cell (first match wins, the engine's own
cond_css_for_cell order): matched cells' text_dump entries get a
"!<marker>" suffix ("!bar<N>" for data-bar bucket N = fill-percent/10,
"!above"/"!below"/"!dup"/"!uniq" for the average/occurrence kinds, "!hi"
for plain highlight kinds), and the cell widget carries the matching cf-*
CSS class painted by office_gui_sheet_minimal_css on the pixel path.
Evaluation is cond_format.spl's own (cond_rule_matches_cell /
cond_data_bar_percent) -- nothing is re-decided in the GUI layer.

Hand-computed ground truth used below:
- data_bar over 10,20,30,40,50 (A1:A5): P = (v-10)/(50-10)*100 gives
  0/25/50/75/100, so buckets P/10 are 0/2/5/7/10.
- above_average over 5,3,8,3,6 (A1:A5): mean = (5+3+8+3+6)/5 = 25/5 = 5;
  strictly above -> ONLY 8 and 6 match (the two 3s and the 5 itself do not).
- duplicate/unique over "a","b","a" (A1:A3): "a" occurs twice (duplicate),
  "b" once (unique).

## Scenarios

### sheet_gui_view_with_formats: data-bar buckets

#### the range minimum gets bucket 0 (P = (10-10)/40*100 = 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _bar_demo_sheet()
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A5", kind: "data_bar", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 5, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|10!bar0")
```

</details>

#### the midpoint gets bucket 5 (P = (30-10)/40*100 = 50)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _bar_demo_sheet()
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A5", kind: "data_bar", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 5, 1)
val lines = view.text_dump.split("\n")
expect(lines[4]).to_equal("3|30!bar5")
```

</details>

#### the range maximum gets bucket 10 (P = (50-10)/40*100 = 100)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _bar_demo_sheet()
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A5", kind: "data_bar", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 5, 1)
val lines = view.text_dump.split("\n")
expect(lines[6]).to_equal("5|50!bar10")
```

</details>

#### quarter stops land on buckets 2 and 7 (P = 25 and 75)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _bar_demo_sheet()
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A5", kind: "data_bar", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 5, 1)
val lines = view.text_dump.split("\n")
expect(lines[3]).to_equal("2|20!bar2")
expect(lines[5]).to_equal("4|40!bar7")
```

</details>

#### a degenerate single-value range gets the full bar (bucket 10)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("One")
sheet.set_value("A1", "7")
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A1", kind: "data_bar", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 1, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|7!bar10")
```

</details>

### sheet_gui_view_with_formats: above-average matches

#### marks exactly the cells strictly above the hand-computed mean of 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _score_demo_sheet()
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A5", kind: "above_average", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 5, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|5")
expect(lines[3]).to_equal("2|3")
expect(lines[4]).to_equal("3|8!above")
expect(lines[5]).to_equal("4|3")
expect(lines[6]).to_equal("5|6!above")
```

</details>

#### below_average marks the complementary strict side (the two 3s only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _score_demo_sheet()
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A5", kind: "below_average", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 5, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|5")
expect(lines[3]).to_equal("2|3!below")
expect(lines[4]).to_equal("3|8")
expect(lines[5]).to_equal("4|3!below")
expect(lines[6]).to_equal("5|6")
```

</details>

### sheet_gui_view_with_formats: duplicate and unique matches

#### duplicate marks the two 'a' cells only

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _text_demo_sheet()
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A3", kind: "duplicate", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 3, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|a!dup")
expect(lines[3]).to_equal("2|b")
expect(lines[4]).to_equal("3|a!dup")
```

</details>

#### unique marks the single 'b' cell only

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _text_demo_sheet()
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A3", kind: "unique", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 3, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|a")
expect(lines[3]).to_equal("2|b!uniq")
expect(lines[4]).to_equal("3|a")
```

</details>

### sheet_gui_view_with_formats: highlight kinds and selection

#### a cell_value '>100' rule marks only the matching cell with !hi

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Vals")
sheet.set_value("A1", "150")
sheet.set_value("A2", "50")
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A2", kind: "cell_value", criteria: ">100", n: 0, css: "background:#fde7e9")]
val view = sheet_gui_view_with_formats(session, rules, 2, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|150!hi")
expect(lines[3]).to_equal("2|50")
```

</details>

#### a selected matched cell shows bracket form plus the marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _bar_demo_sheet()
val session = session_new(sheet, "A1")
val rules: [CondRule] = [CondRule(range: "A1:A5", kind: "data_bar", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 5, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|[10]!bar0")
```

</details>

### sheet_gui_cf_html: cf classes land in the rendered page HTML

#### matched cells' class attributes carry their cf classes; unmatched cells stay plain

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Html")
sheet.set_value("A1", "10")
sheet.set_value("A2", "50")
sheet.set_value("A3", "x")
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "A1:A2", kind: "data_bar", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 3, 1)
val html = sheet_gui_cf_html(view, "")
expect(html).to_contain("class=\"widget-text cf-bar-0\" id=\"cell_A1\"")
expect(html).to_contain("class=\"widget-text cf-bar-10\" id=\"cell_A2\"")
expect(html).to_contain("class=\"widget-text\" id=\"cell_A3\"")
expect(html).to_contain(".cf-bar-10{background:#638ec6;}")
```

</details>

### sheet_gui_view_with_formats: no rules and fail-closed edges

#### an empty rule list renders byte-identically to sheet_gui_view_with_selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Plain")
sheet.set_value("A1", "1")
sheet.set_value("B2", "x")
val session = session_new(sheet, "B2")
val no_rules: [CondRule] = []
val cf_view = sheet_gui_view_with_formats(session, no_rules, 3, 2)
val plain_view = sheet_gui_view_with_selection(session, 3, 2)
expect(cf_view.text_dump).to_equal(plain_view.text_dump)
```

</details>

#### rules over an all-empty range fail closed (dump identical to plain view)

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Empty")
sheet.set_value("A1", "9")
val session = session_new(sheet, "")
# B1:B2 is INSIDE the rendered 2x2 window but holds only empty
# cells: data_bar sees non-numeric cells (-1, no match) and
# above_average sees an empty mean population (no match).
val rules: [CondRule] = [
    CondRule(range: "B1:B2", kind: "data_bar", criteria: "", n: 0, css: ""),
    CondRule(range: "B1:B2", kind: "above_average", criteria: "", n: 0, css: "")
]
val cf_view = sheet_gui_view_with_formats(session, rules, 2, 2)
val plain_view = sheet_gui_view_with_selection(session, 2, 2)
expect(cf_view.text_dump).to_equal(plain_view.text_dump)
```

</details>

#### a rule with an unparseable range never matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Bad")
sheet.set_value("A1", "9")
val session = session_new(sheet, "")
val rules: [CondRule] = [CondRule(range: "", kind: "data_bar", criteria: "", n: 0, css: "")]
val view = sheet_gui_view_with_formats(session, rules, 1, 1)
val lines = view.text_dump.split("\n")
expect(lines[2]).to_equal("1|9")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
