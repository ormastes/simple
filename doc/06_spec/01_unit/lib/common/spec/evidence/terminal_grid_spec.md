# Terminal grid evidence (E2)

> For QA authors building TUI scenario evidence: this spec documents the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Terminal grid evidence (E2)

For QA authors building TUI scenario evidence: this spec documents the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Lane E2 of doc/03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md |
| Source | `test/01_unit/lib/common/spec/evidence/terminal_grid_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

For QA authors building TUI scenario evidence: this spec documents the
cell-accurate terminal snapshot model, its width policy, and the four
fail-closed rules that keep a TUI capture from reporting a clean pass over a
broken render.

## Primary Workflow

A provider builds a `TerminalSnapshot` from rendered rows, declares semantic
regions over it, and projects it to `CanonicalEvidence` for
`compare_evidence`. The same snapshot also yields a human-readable text
projection for the manual and a cell-level diff for QA triage.

## Scenarios

### Terminal snapshot construction

#### builds one cell per plain-ASCII grapheme

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Build a snapshot from a single plain row
- Verify the projected text keeps the row content
   - Expected: terminal_text_projection(snapshot)[0] equals `hi  `


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-TUI-001
step("Build a snapshot from a single plain row")
val snapshot = terminal_snapshot_from_rows(["hi"], 4)
step("Verify the projected text keeps the row content")
expect(terminal_text_projection(snapshot)[0]).to_equal("hi  ")
```

</details>

#### widens the grid for double-width graphemes and adds a continuation cell

- widens the grid for double-width graphemes and adds a continuation cell
- Build a snapshot from a row containing a wide CJK character
- Verify the wide character round-trips through the text projection
   - Expected: terminal_text_projection(snapshot)[0] equals `中文`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("widens the grid for double-width graphemes and adds a continuation cell")
step("Build a snapshot from a row containing a wide CJK character")
val snapshot = terminal_snapshot_from_rows(["中文"], 4)
step("Verify the wide character round-trips through the text projection")
expect(terminal_text_projection(snapshot)[0]).to_equal("中文")
```

</details>

#### folds a combining mark onto the previous cell without advancing the column

- folds a combining mark onto the previous cell without advancing the column
- Build a snapshot from a base letter followed by a combining acute accent, sized to fit exactly
- Verify the combining mark did not consume its own column
   - Expected: terminal_text_projection(snapshot)[0] equals `éx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("folds a combining mark onto the previous cell without advancing the column")
step("Build a snapshot from a base letter followed by a combining acute accent, sized to fit exactly")
val snapshot = terminal_snapshot_from_rows(["éx"], 2)
step("Verify the combining mark did not consume its own column")
expect(terminal_text_projection(snapshot)[0]).to_equal("éx")
```

</details>

#### keeps an emoji as a single double-width cell

- keeps an emoji as a single double-width cell
- Build a snapshot from a row containing an emoji
- Verify the emoji and trailing glyph both round-trip
   - Expected: terminal_text_projection(snapshot)[0] equals `😀!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps an emoji as a single double-width cell")
step("Build a snapshot from a row containing an emoji")
val snapshot = terminal_snapshot_from_rows(["😀!"], 3)
step("Verify the emoji and trailing glyph both round-trip")
expect(terminal_text_projection(snapshot)[0]).to_equal("😀!")
```

</details>

#### reports width 0/1/2 from the explicit width table

- reports width 0/1/2 from the explicit width table
- Check a combining mark reports width 0
   - Expected: display_width_of("́") equals `0`
- Check plain ASCII reports width 1
   - Expected: display_width_of("a") equals `1`
- Check a wide CJK character reports width 2
   - Expected: display_width_of("中") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports width 0/1/2 from the explicit width table")
step("Check a combining mark reports width 0")
expect(display_width_of("́")).to_equal(0)
step("Check plain ASCII reports width 1")
expect(display_width_of("a")).to_equal(1)
step("Check a wide CJK character reports width 2")
expect(display_width_of("中")).to_equal(2)
```

</details>

### Rule: a snapshot with no width profile is invalid

#### rejects a snapshot whose width_profile was never set

- rejects a snapshot whose width_profile was never set
- Build a snapshot struct directly with an empty width_profile
- Verify the snapshot is flagged invalid
   - Expected: terminal_snapshot_is_valid(snapshot) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a snapshot whose width_profile was never set")
step("Build a snapshot struct directly with an empty width_profile")
val snapshot = TerminalSnapshot(
    columns: 4,
    rows: 1,
    cells: [terminal_cell_default()],
    cursor: TerminalCursor(row: 0, col: 0, visible: false),
    width_profile: "",
    semantic_regions: []
)
step("Verify the snapshot is flagged invalid")
expect(terminal_snapshot_is_valid(snapshot)).to_equal(false)
```

</details>

#### fails evidence projection for an invalid snapshot instead of emitting empty nodes

- fails evidence projection for an invalid snapshot instead of emitting empty nodes
- Build an invalid snapshot with an empty width_profile
- Project the snapshot to evidence
- Verify the projection reports a parse failure, not an empty node set
   - Expected: evidence.parse_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails evidence projection for an invalid snapshot instead of emitting empty nodes")
step("Build an invalid snapshot with an empty width_profile")
val snapshot = TerminalSnapshot(
    columns: 4,
    rows: 1,
    cells: [terminal_cell_default()],
    cursor: TerminalCursor(row: 0, col: 0, visible: false),
    width_profile: "",
    semantic_regions: []
)
step("Project the snapshot to evidence")
val evidence = terminal_snapshot_to_evidence(snapshot, "profile/1")
step("Verify the projection reports a parse failure, not an empty node set")
expect(evidence.parse_ok).to_equal(false)
```

</details>

### Rule: a region that resolves to no cells is an error, not empty text

#### fails when the declared region node_id does not exist on the snapshot

- fails when the declared region node_id does not exist on the snapshot
- Build a snapshot with no semantic regions declared
- Resolve a region that was never declared
- Verify resolution is flagged as failed, not as empty text
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails when the declared region node_id does not exist on the snapshot")
step("Build a snapshot with no semantic regions declared")
val snapshot = terminal_snapshot_from_rows(["hello"], 6)
step("Resolve a region that was never declared")
val (text_value, clipped, ok) = scoped_region_text_detailed(snapshot, "main#missing")
step("Verify resolution is flagged as failed, not as empty text")
expect(ok).to_equal(false)
```

</details>

#### fails when the declared region has zero width or height

- fails when the declared region has zero width or height
- Build a snapshot with a zero-height region
- Resolve the zero-height region
- Verify resolution is flagged as failed
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails when the declared region has zero width or height")
step("Build a snapshot with a zero-height region")
val snapshot = snapshot_with_region(["hello"], 6, "main#empty", 0, 0, 3, 0)
step("Resolve the zero-height region")
val (text_value, clipped, ok) = scoped_region_text_detailed(snapshot, "main#empty")
step("Verify resolution is flagged as failed")
expect(ok).to_equal(false)
```

</details>

#### succeeds and returns the rendered text for a properly declared region

- succeeds and returns the rendered text for a properly declared region
- Build a snapshot with a one-row region over 'hello'
- Resolve the declared region
- Verify the region text matches the rendered content
   - Expected: text_value equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("succeeds and returns the rendered text for a properly declared region")
step("Build a snapshot with a one-row region over 'hello'")
val snapshot = snapshot_with_region(["hello "], 6, "main#label", 0, 0, 5, 1)
step("Resolve the declared region")
val text_value = scoped_region_text(snapshot, "main#label")
step("Verify the region text matches the rendered content")
expect(text_value).to_equal("hello")
```

</details>

### Rule: a double-width grapheme clipped at the right edge is reported

#### flags clipping when a region's right edge splits a wide grapheme

- flags clipping when a region's right edge splits a wide grapheme
- Build a snapshot with a wide character straddling the region boundary
- Resolve the clipped region
- Verify the resolution reports the clip rather than silently truncating
   - Expected: clipped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flags clipping when a region's right edge splits a wide grapheme")
step("Build a snapshot with a wide character straddling the region boundary")
val snapshot = snapshot_with_region(["a中b"], 4, "main#clip", 0, 0, 2, 1)
step("Resolve the clipped region")
val (text_value, clipped, ok) = scoped_region_text_detailed(snapshot, "main#clip")
step("Verify the resolution reports the clip rather than silently truncating")
expect(clipped).to_equal(true)
```

</details>

#### does not flag clipping when the region boundary falls between cells

- does not flag clipping when the region boundary falls between cells
- Build a snapshot where the region boundary lands cleanly
- Resolve the cleanly bounded region
- Verify no clip was reported
   - Expected: clipped is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not flag clipping when the region boundary falls between cells")
step("Build a snapshot where the region boundary lands cleanly")
val snapshot = snapshot_with_region(["ab中"], 4, "main#clean", 0, 0, 2, 1)
step("Resolve the cleanly bounded region")
val (text_value, clipped, ok) = scoped_region_text_detailed(snapshot, "main#clean")
step("Verify no clip was reported")
expect(clipped).to_equal(false)
```

</details>

### Rule: a continuation cell never contributes its own grapheme to region text

#### renders a wide grapheme's region text without a duplicated character

- renders a wide grapheme's region text without a duplicated character
- Build a snapshot with one wide grapheme filling a two-column region
- Resolve the region
- Verify the region text contains the grapheme exactly once
   - Expected: text_value equals `中`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders a wide grapheme's region text without a duplicated character")
step("Build a snapshot with one wide grapheme filling a two-column region")
val snapshot = snapshot_with_region(["中"], 4, "main#wide", 0, 0, 2, 1)
step("Resolve the region")
val text_value = scoped_region_text(snapshot, "main#wide")
step("Verify the region text contains the grapheme exactly once")
expect(text_value).to_equal("中")
```

</details>

#### excludes continuation cells from the whole-grid text projection

- excludes continuation cells from the whole-grid text projection
- Build a snapshot mixing a wide grapheme with plain text
- Project the whole grid to text
- Verify the continuation cell contributed no extra character
   - Expected: line equals `中ab `


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("excludes continuation cells from the whole-grid text projection")
step("Build a snapshot mixing a wide grapheme with plain text")
val snapshot = terminal_snapshot_from_rows(["中ab"], 5)
step("Project the whole grid to text")
val line = terminal_text_projection(snapshot)[0]
step("Verify the continuation cell contributed no extra character")
expect(line).to_equal("中ab ")
```

</details>

### Evidence projection

#### emits grid metadata and region nodes for a valid snapshot

- emits grid metadata and region nodes for a valid snapshot
- Build a valid snapshot with one declared region
- Project the snapshot to canonical evidence
- Verify the projection parsed successfully
   - Expected: evidence.parse_ok is true
- Verify the region node carries the rendered region text
   - Expected: evidence.nodes[3].path equals `main#status`
   - Expected: evidence.nodes[3].value equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits grid metadata and region nodes for a valid snapshot")
step("Build a valid snapshot with one declared region")
val snapshot = snapshot_with_region(["ok    "], 6, "main#status", 0, 0, 2, 1)
step("Project the snapshot to canonical evidence")
val evidence = terminal_snapshot_to_evidence(snapshot, "tui/profile-1")
step("Verify the projection parsed successfully")
expect(evidence.parse_ok).to_equal(true)
step("Verify the region node carries the rendered region text")
expect(evidence.nodes[3].path).to_equal("main#status")
expect(evidence.nodes[3].value).to_equal("ok")
```

</details>

#### emits columns/rows/width_profile as metadata nodes

- emits columns/rows/width_profile as metadata nodes
- Build a valid 6x1 snapshot
- Project the snapshot to canonical evidence
- Verify columns, rows, and width_profile are all present
   - Expected: evidence.nodes[0].path equals `terminal.columns`
   - Expected: evidence.nodes[0].value equals `6`
   - Expected: evidence.nodes[1].path equals `terminal.rows`
   - Expected: evidence.nodes[1].value equals `1`
   - Expected: evidence.nodes[2].path equals `terminal.width_profile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits columns/rows/width_profile as metadata nodes")
step("Build a valid 6x1 snapshot")
val snapshot = terminal_snapshot_from_rows(["abcdef"], 6)
step("Project the snapshot to canonical evidence")
val evidence = terminal_snapshot_to_evidence(snapshot, "tui/profile-1")
step("Verify columns, rows, and width_profile are all present")
expect(evidence.nodes[0].path).to_equal("terminal.columns")
expect(evidence.nodes[0].value).to_equal("6")
expect(evidence.nodes[1].path).to_equal("terminal.rows")
expect(evidence.nodes[1].value).to_equal("1")
expect(evidence.nodes[2].path).to_equal("terminal.width_profile")
```

</details>

### Cell-level diff

#### reports no differences for two identical snapshots

- reports no differences for two identical snapshots
- Build two identical snapshots
- Diff the snapshots
- Verify the diff is empty
   - Expected: diff.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports no differences for two identical snapshots")
step("Build two identical snapshots")
val expected = terminal_snapshot_from_rows(["match"], 5)
val actual = terminal_snapshot_from_rows(["match"], 5)
step("Diff the snapshots")
val diff = terminal_cell_diff(expected, actual)
step("Verify the diff is empty")
expect(diff.len()).to_equal(0)
```

</details>

#### reports the row, column, and both graphemes for a differing cell

- reports the row, column, and both graphemes for a differing cell
- Build two snapshots that differ in one cell
- Diff the snapshots
- Verify the single differing cell is reported with both graphemes
   - Expected: diff.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the row, column, and both graphemes for a differing cell")
step("Build two snapshots that differ in one cell")
val expected = terminal_snapshot_from_rows(["cat"], 3)
val actual = terminal_snapshot_from_rows(["car"], 3)
step("Diff the snapshots")
val diff = terminal_cell_diff(expected, actual)
step("Verify the single differing cell is reported with both graphemes")
expect(diff.len()).to_equal(1)
expect(diff[0]).to_contain("row 0 col 2")
expect(diff[0]).to_contain("t")
expect(diff[0]).to_contain("r")
```

</details>

#### reports a size mismatch line when grids differ in shape

- reports a size mismatch line when grids differ in shape
- Build two snapshots of different column counts
- Diff the snapshots
- Verify the size mismatch is reported


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a size mismatch line when grids differ in shape")
step("Build two snapshots of different column counts")
val expected = terminal_snapshot_from_rows(["ab"], 2)
val actual = terminal_snapshot_from_rows(["ab"], 4)
step("Diff the snapshots")
val diff = terminal_cell_diff(expected, actual)
step("Verify the size mismatch is reported")
expect(diff[0]).to_contain("grid size mismatch")
```

</details>

### Red-team hardening: region bounds

#### rejects a region wider than the grid instead of fabricating columns

- Project the oversized region through the scoped text projection
- Verify the projection fails closed instead of fabricating blank columns
   - Expected: text_value equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-TUI-001
step("Project the oversized region through the scoped text projection")
val (text_value, _clipped, ok) = scoped_region_text_detailed(tiny_snapshot(), "oversized")
step("Verify the projection fails closed instead of fabricating blank columns")
assert_false(ok)
expect(text_value).to_equal("")
```

</details>

#### rejects a region placed off the grid

- Project the off-grid region through the scoped text projection
- Verify the projection fails closed instead of inventing rows
   - Expected: text_value equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-TUI-001
step("Project the off-grid region through the scoped text projection")
val (text_value, _clipped, ok) = scoped_region_text_detailed(tiny_snapshot(), "offgrid")
step("Verify the projection fails closed instead of inventing rows")
assert_false(ok)
expect(text_value).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-SSPEC-TUI-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8872be74278cd6bf2215182baae17d3bb3a0128bbc32557651de1cfb2a39fccf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8872be74278cd6bf2215182baae17d3bb3a0128bbc32557651de1cfb2a39fccf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8872be74278cd6bf2215182baae17d3bb3a0128bbc32557651de1cfb2a39fccf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/spec/evidence/terminal_grid_spec.spl
mirror: doc/06_spec/01_unit/lib/common/spec/evidence/terminal_grid_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/spec/evidence/terminal_grid_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/spec/evidence/terminal_grid_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/spec/evidence/terminal_grid_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/spec/evidence/terminal_grid_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds one cell per plain-ASCII grapheme' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/terminal_grid_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'widens the grid for double-width graphemes and adds a continuation cell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/terminal_grid_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'folds a combining mark onto the previous cell without advancing the column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
