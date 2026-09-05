# Block Model Specification

> Tests covering markdown block model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Block Model Specification

## Scenarios

### markdown block model

#### parses source ranges and common markdown block kinds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses source ranges and common markdown block kinds
   - Expected: model.block_count() equals `6`
   - Expected: model.block_at(0).kind equals `heading`
   - Expected: model.block_at(0).from_line equals `0`
   - Expected: model.block_at(1).kind equals `paragraph`
   - Expected: model.block_at(2).kind equals `list`
   - Expected: model.block_at(3).kind equals `table`
   - Expected: model.block_at(3).from_line equals `6`
   - Expected: model.block_at(3).to_line equals `8`
   - Expected: model.block_at(4).kind equals `callout`
   - Expected: model.block_at(5).kind equals `embed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses source ranges and common markdown block kinds")
val source = "# Title\n\nParagraph text\n\n- [ ] Task\n\n| A | B |\n| --- | --- |\n| 1 | 2 |\n\n> [!NOTE]- Folded\n> Body\n\n![Diagram](assets/a.png)\n\n```sdn-graph\nA -> B\n```"
val model = BlockModel.from_markdown(source)

expect(model.block_count()).to_equal(6)
expect(model.block_at(0).kind).to_equal("heading")
expect(model.block_at(0).from_line).to_equal(0)
expect(model.block_at(1).kind).to_equal("paragraph")
expect(model.block_at(2).kind).to_equal("list")
expect(model.block_at(3).kind).to_equal("table")
expect(model.block_at(3).from_line).to_equal(6)
expect(model.block_at(3).to_line).to_equal(8)
expect(model.block_at(4).kind).to_equal("callout")
expect(model.block_at(5).kind).to_equal("embed")
```

</details>

#### tracks active block and cursor mapping

- tracks active block and cursor mapping
   - Expected: model.block_for_line(2) equals `1`
   - Expected: bm_cursor_block_index(model, 5) equals `2`
   - Expected: bm_cursor_block_changed(model, 2) is true
   - Expected: model.active_block equals `1`
   - Expected: model.is_active(1) is true
   - Expected: bm_cursor_block_changed(model, 2) is false
   - Expected: bm_active_block_range(model) equals `2`
   - Expected: render_block_line_span(model.block_at(1)) equals `2`
   - Expected: model.active_block equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks active block and cursor mapping")
var model = BlockModel.from_markdown("# Title\n\nFirst paragraph\nsecond line\n\n## Next")

expect(model.block_for_line(2)).to_equal(1)
expect(bm_cursor_block_index(model, 5)).to_equal(2)
expect(bm_cursor_block_changed(model, 2)).to_equal(true)

model.activate_block(1)
expect(model.active_block).to_equal(1)
expect(model.is_active(1)).to_equal(true)
expect(bm_cursor_block_changed(model, 2)).to_equal(false)
expect(bm_active_block_range(model)).to_equal(2)
expect(render_block_line_span(model.block_at(1))).to_equal(2)

model.deactivate_block()
expect(model.active_block).to_equal(-1)
```

</details>

#### rebuilds blocks and resets active state

- rebuilds blocks and resets active state
   - Expected: model.block_count() equals `1`
   - Expected: model.block_at(0).kind equals `paragraph`
   - Expected: model.active_block equals `-1`
   - Expected: model.next_id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rebuilds blocks and resets active state")
var model = BlockModel.from_markdown("# Old")
model.activate_block(0)
model.rebuild("plain\ntext")

expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("paragraph")
expect(model.active_block).to_equal(-1)
expect(model.next_id).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/editor/block_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering markdown block model.
- markdown block model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0055cafabe294da053e670f072a4358af37ca0c698d21d5ce87ec215efb8556f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0055cafabe294da053e670f072a4358af37ca0c698d21d5ce87ec215efb8556f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0055cafabe294da053e670f072a4358af37ca0c698d21d5ce87ec215efb8556f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/editor/block_model_spec.spl
mirror: doc/06_spec/unit/lib/editor/block_model_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/editor/block_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/editor/block_model_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/editor/block_model_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/editor/block_model_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses source ranges and common markdown block kinds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/editor/block_model_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks active block and cursor mapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/editor/block_model_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rebuilds blocks and resets active state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
