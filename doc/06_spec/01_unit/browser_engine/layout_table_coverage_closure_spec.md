# CSS Table Structure Helpers — Coverage Closure

> Purpose: Prove that _find_table_node.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Table Structure Helpers — Coverage Closure

Purpose: Prove that _find_table_node.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/layout_table_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that _find_table_node.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### _find_table_node

#### returns the node itself when it is a table

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns the node itself when it is a table
- Verify: returns the node itself when it is a table
   - Expected: _find_table_node(t).tag_name equals `table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the node itself when it is a table")
step("Verify: returns the node itself when it is a table")
# @req: REQ-BROWSER-ENGINE-LAYOUT-TABLE-COVERAGE-CLOSURE-SPEC-SPL-001
val t = BeDomNode.element("table")
expect(_find_table_node(t).tag_name).to_equal("table")
```

</details>

#### finds a nested table inside wrappers

- finds a nested table inside wrappers
- Verify: finds a nested table inside wrappers
   - Expected: _find_table_node(outer).tag_name equals `table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("finds a nested table inside wrappers")
step("Verify: finds a nested table inside wrappers")
var outer = BeDomNode.element("div")
var inner = BeDomNode.element("section")
inner.add_child(BeDomNode.element("table"))
outer.add_child(BeDomNode.element("p"))
outer.add_child(inner)
expect(_find_table_node(outer).tag_name).to_equal("table")
```

</details>

#### returns the input node when no table exists

- returns the input node when no table exists
- Verify: returns the input node when no table exists
   - Expected: _find_table_node(d).tag_name equals `div`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the input node when no table exists")
step("Verify: returns the input node when no table exists")
var d = BeDomNode.element("div")
d.add_child(BeDomNode.element("span"))
expect(_find_table_node(d).tag_name).to_equal("div")
```

</details>

### _collect_table_rows / _collect_cells

#### collects direct tr children and tr inside tbody/thead/tfoot

- collects direct tr children and tr inside tbody/thead/tfoot
- Verify: collects direct tr children and tr inside tbody/thead/tfoot
   - Expected: _collect_table_rows(table).len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("collects direct tr children and tr inside tbody/thead/tfoot")
step("Verify: collects direct tr children and tr inside tbody/thead/tfoot")
var table = BeDomNode.element("table")
table.add_child(BeDomNode.element("tr"))
var thead = BeDomNode.element("thead")
thead.add_child(BeDomNode.element("tr"))
var tbody = BeDomNode.element("tbody")
tbody.add_child(BeDomNode.element("tr"))
tbody.add_child(BeDomNode.element("caption"))
table.add_child(thead)
table.add_child(tbody)
table.add_child(BeDomNode.element("caption"))
expect(_collect_table_rows(table).len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### collects only td/th cells from a row

- collects only td/th cells from a row
- Verify: collects only td/th cells from a row
   - Expected: _collect_cells(row).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("collects only td/th cells from a row")
step("Verify: collects only td/th cells from a row")
var row = BeDomNode.element("tr")
row.add_child(BeDomNode.element("td"))
row.add_child(BeDomNode.element("th"))
row.add_child(BeDomNode.text(" "))
row.add_child(BeDomNode.element("script"))
expect(_collect_cells(row).len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### _get_colspan

#### defaults to 1 when missing, empty, non-numeric or zero

- defaults to 1 when missing, empty, non-numeric or zero
- Verify: defaults to 1 when missing, empty, non-numeric or zero
   - Expected: _get_colspan(_cell("")) equals `1`
   - Expected: _get_colspan(_cell("abc")) equals `1`
   - Expected: _get_colspan(_cell("0")) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("defaults to 1 when missing, empty, non-numeric or zero")
step("Verify: defaults to 1 when missing, empty, non-numeric or zero")
expect(_get_colspan(_cell(""))).to_equal(1)
expect(_get_colspan(_cell("abc"))).to_equal(1)
expect(_get_colspan(_cell("0"))).to_equal(1)
```

</details>

#### parses multi-digit colspans and ignores stray characters

- parses multi-digit colspans and ignores stray characters
- Verify: parses multi-digit colspans and ignores stray characters
   - Expected: _get_colspan(_cell("12")) equals `12`
   - Expected: _get_colspan(_cell(" 3 ")) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("parses multi-digit colspans and ignores stray characters")
step("Verify: parses multi-digit colspans and ignores stray characters")
expect(_get_colspan(_cell("12"))).to_equal(12)
expect(_get_colspan(_cell(" 3 "))).to_equal(3)
```

</details>

### _count_logical_columns / _compute_col_widths

#### sums colspans and treats an empty row as one column

- sums colspans and treats an empty row as one column
- Verify: sums colspans and treats an empty row as one column
   - Expected: _count_logical_columns(cells) equals `6`
   - Expected: _count_logical_columns(no_cells) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("sums colspans and treats an empty row as one column")
step("Verify: sums colspans and treats an empty row as one column")
val cells = [_cell("2"), _cell(""), _cell("3")]
expect(_count_logical_columns(cells)).to_equal(6)  # oracle: 6 — named expected value from the requirement
var no_cells: [BeDomNode] = []
expect(_count_logical_columns(no_cells)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### distributes remainder pixels to the leftmost columns

- distributes remainder pixels to the leftmost columns
- Verify: distributes remainder pixels to the leftmost columns
   - Expected: w.len() equals `3`
   - Expected: w[0] equals `4`
   - Expected: w[1] equals `3`
   - Expected: w[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("distributes remainder pixels to the leftmost columns")
step("Verify: distributes remainder pixels to the leftmost columns")
val w = _compute_col_widths(10, 3, [])
expect(w.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(w[0]).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(w[1]).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(w[2]).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### returns empty widths for non-positive column counts

- returns empty widths for non-positive column counts
- Verify: returns empty widths for non-positive column counts
   - Expected: _compute_col_widths(10, 0, []).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns empty widths for non-positive column counts")
step("Verify: returns empty widths for non-positive column counts")
expect(_compute_col_widths(10, 0, []).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### simple_web_* HNode table helpers

#### collects rows with their group markers

- collects rows with their group markers
- Verify: collects rows with their group markers
   - Expected: rows.rows.len() equals `2`
   - Expected: rows.groups[0] equals `-1`
   - Expected: rows.groups[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("collects rows with their group markers")
step("Verify: collects rows with their group markers")
val rows = simple_web_collect_table_rows(_arena(), _index(), 0)
expect(rows.rows.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(rows.groups[0]).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(rows.groups[1]).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### clamps cell span to column count and floors at 1

- clamps cell span to column count and floors at 1
- Verify: clamps cell span to column count and floors at 1
   - Expected: simple_web_fixed_table_cell_span(_hnode("td", "td colspan=\"5\""), 3) equals `3`
   - Expected: simple_web_fixed_table_cell_span(_hnode("td", "td"), 3) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("clamps cell span to column count and floors at 1")
step("Verify: clamps cell span to column count and floors at 1")
expect(simple_web_fixed_table_cell_span(_hnode("td", "td colspan=\"5\""), 3)).to_equal(3)
expect(simple_web_fixed_table_cell_span(_hnode("td", "td"), 3)).to_equal(1)
```

</details>

#### counts row columns from colspans, minimum 1

- counts row columns from colspans, minimum 1
- Verify: counts row columns from colspans, minimum 1
   - Expected: simple_web_fixed_table_row_column_count(_arena(), _index(), 1) equals `3`
   - Expected: simple_web_fixed_table_row_column_count(_arena(), _index(), 3) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("counts row columns from colspans, minimum 1")
step("Verify: counts row columns from colspans, minimum 1")
expect(simple_web_fixed_table_row_column_count(_arena(), _index(), 1)).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(simple_web_fixed_table_row_column_count(_arena(), _index(), 3)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### takes the max row column count across the table

- takes the max row column count across the table
- Verify: takes the max row column count across the table
   - Expected: simple_web_fixed_table_column_count(_arena(), _index(), rows) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("takes the max row column count across the table")
step("Verify: takes the max row column count across the table")
val rows = simple_web_collect_table_rows(_arena(), _index(), 0)
expect(simple_web_fixed_table_column_count(_arena(), _index(), rows)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-BROWSER-ENGINE-LAYOUT-TABLE-COVERAGE-CLOSURE-SPEC-SPL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a8adc1a98e1515669e7952976a49f030016b388aa1aa132c59db2e7f91aa217`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a8adc1a98e1515669e7952976a49f030016b388aa1aa132c59db2e7f91aa217`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a8adc1a98e1515669e7952976a49f030016b388aa1aa132c59db2e7f91aa217`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/layout_table_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/layout_table_coverage_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/layout_table_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/layout_table_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/layout_table_coverage_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/layout_table_coverage_closure_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the node itself when it is a table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/layout_table_coverage_closure_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds a nested table inside wrappers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/layout_table_coverage_closure_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the input node when no table exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
