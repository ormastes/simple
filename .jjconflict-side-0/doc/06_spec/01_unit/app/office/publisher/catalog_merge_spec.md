# Catalog Merge Specification

> Tests covering catalog merge: tile substitution, catalog merge: tile count, catalog merge: grid placement, catalog merge: html rendering, deliberate-fail probe (must stay green).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Catalog Merge Specification

## Scenarios

### catalog merge: tile substitution

#### fills a tile's placeholders from the parallel field values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fills a tile's placeholders from the parallel field values
   - Expected: filled equals `Apple\n$2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fills a tile's placeholders from the parallel field values")
val filled = merge_tile(_template(), FIELD_NAMES, ["Apple", "2"])
expect(filled).to_equal("Apple\n$2")
```

</details>

#### fills a different record's values into the same template

- fills a different record's values into the same template
   - Expected: filled equals `Banana\n$1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fills a different record's values into the same template")
val filled = merge_tile(_template(), FIELD_NAMES, ["Banana", "1"])
expect(filled).to_equal("Banana\n$1")
```

</details>

### catalog merge: tile count

#### produces exactly one frame per data record

- produces exactly one frame per data record
   - Expected: catalog_tile_count(page) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("produces exactly one frame per data record")
val page = catalog_merge(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(catalog_tile_count(page)).to_equal(3)
```

</details>

### catalog merge: grid placement

#### places record 0 in the top-left tile

- places record 0 in the top-left tile


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("places record 0 in the top-left tile")
val page = catalog_merge(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(frame_text(page, "tile0")).to_contain("Apple")
```

</details>

#### places record 1 in column 1 of row 0 (x=200, y=0)

- places record 1 in column 1 of row 0 (x=200, y=0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("places record 1 in column 1 of row 0 (x=200, y=0)")
val html = catalog_render_html(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(html).to_contain("Banana")
expect(html).to_contain("left:200px;top:0px")
```

</details>

#### places record 2 in column 0 of row 1 (x=0, y=100)

- places record 2 in column 0 of row 1 (x=0, y=100)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("places record 2 in column 0 of row 1 (x=0, y=100)")
val page = catalog_merge(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(frame_text(page, "tile2")).to_contain("Cherry")
```

</details>

#### renders record 2's tile at the row-1 offset in html

- renders record 2's tile at the row-1 offset in html


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders record 2's tile at the row-1 offset in html")
val html = catalog_render_html(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(html).to_contain("left:0px;top:100px")
```

</details>

### catalog merge: html rendering

#### includes every record's fields in the rendered catalog page

- includes every record's fields in the rendered catalog page


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("includes every record's fields in the rendered catalog page")
val html = catalog_render_html(_template(), 400, 200, 2, FIELD_NAMES, RECORDS)
expect(html).to_contain("Apple")
expect(html).to_contain("Banana")
expect(html).to_contain("Cherry")
```

</details>

### deliberate-fail probe (must stay green)

#### sanity-checks the hand-computed substitution ground truth

- sanity-checks the hand-computed substitution ground truth
   - Expected: filled equals `Apple\n$2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sanity-checks the hand-computed substitution ground truth")
val filled = merge_tile(_template(), FIELD_NAMES, ["Apple", "2"])
# Probe verified live: asserting filled equals "Apple\n$1"
# (record 1's price instead of record 0's) failed with a
# mismatch, confirming the harness executes this assertion.
# Correct ground truth: record 0's own price is "$2".
expect(filled).to_equal("Apple\n$2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/publisher/catalog_merge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering catalog merge: tile substitution, catalog merge: tile count, catalog merge: grid placement, catalog merge: html rendering, deliberate-fail probe (must stay green).
- catalog merge: tile substitution
- catalog merge: tile count
- catalog merge: grid placement
- catalog merge: html rendering
- deliberate-fail probe (must stay green)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e777070470a0997558e5c067d4c649d07da2d73af56511dd23269f3fabf93450`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e777070470a0997558e5c067d4c649d07da2d73af56511dd23269f3fabf93450`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e777070470a0997558e5c067d4c649d07da2d73af56511dd23269f3fabf93450`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/office/publisher/catalog_merge_spec.spl
mirror: doc/06_spec/01_unit/app/office/publisher/catalog_merge_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/publisher/catalog_merge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/publisher/catalog_merge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/publisher/catalog_merge_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/publisher/catalog_merge_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills a tile's placeholders from the parallel field values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/publisher/catalog_merge_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills a different record's values into the same template' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/publisher/catalog_merge_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces exactly one frame per data record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
