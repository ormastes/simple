# empty_block_margin_self_collapse_spec

> Empty-Block Margin Self-Collapse Spec

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# empty_block_margin_self_collapse_spec

Empty-Block Margin Self-Collapse Spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/empty_block_margin_self_collapse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Empty-Block Margin Self-Collapse Spec

CSS 2.2 §8.3.1: a block with no border, padding, or content collapses its own
top and bottom margins into a single margin, which then collapses with the
adjacent siblings' margins. Chromium (Electron) and WebKitGTK (Tauri2's Linux
engine) both do this; the pure-Simple web lane did not, so every blank markdown
line in the office WYSIWYG preview (an empty <p> with 1em margins) pushed the
following blocks ~20px lower per blank line than the Electron/Tauri hosts —
found by three-host office capture diff (build/office_parity, 2026-08-19).

@tag: rendering, simple-web, layout, margin-collapse, office
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl 5%

## Scenarios

### empty block margin self-collapse

#### renders an empty margined block as contributing no extra vertical space

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders an empty margined block as contributing no extra vertical space
- Render red/blue blocks with 16px margins and no empty block between
- Render the same pair with an empty 16px-margined <p> between them
- Both layouts must be identical: the empty block self-collapses
   - Expected: base.0 equals `0`
   - Expected: with_empty.0 equals `0`
   - Expected: base.1 >= 0 is true
   - Expected: with_empty.1 equals `base.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders an empty margined block as contributing no extra vertical space")
step("Render red/blue blocks with 16px margins and no empty block between")
val base = _render_rows("")
step("Render the same pair with an empty 16px-margined <p> between them")
val with_empty = _render_rows(
    "<p style=\"margin-top:16px;margin-bottom:16px\"></p>")
step("Both layouts must be identical: the empty block self-collapses")
expect(base.0).to_equal(0)
expect(with_empty.0).to_equal(0)
expect(base.1 >= 0).to_equal(true)
expect(with_empty.1).to_equal(base.1)
```

</details>

#### collapses a run of empty blocks the same as one

- collapses a run of empty blocks the same as one
- Render with three consecutive empty margined paragraphs
- The run must add no vertical space either
   - Expected: trio.1 equals `base.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("collapses a run of empty blocks the same as one")
step("Render with three consecutive empty margined paragraphs")
val trio = _render_rows(
    "<p style=\"margin:16px 0\"></p><p style=\"margin:16px 0\"></p>" +
    "<p style=\"margin:16px 0\"></p>")
val base = _render_rows("")
step("The run must add no vertical space either")
expect(trio.1).to_equal(base.1)
```

</details>

#### does not self-collapse an empty block with padding

- does not self-collapse an empty block with padding
- An empty block with 4px vertical padding keeps its box
- Blue block must sit lower than the collapsed baseline
   - Expected: padded.1 > base.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not self-collapse an empty block with padding")
step("An empty block with 4px vertical padding keeps its box")
val padded = _render_rows(
    "<p style=\"margin-top:16px;margin-bottom:16px;padding:4px 0\"></p>")
val base = _render_rows("")
step("Blue block must sit lower than the collapsed baseline")
expect(padded.1 > base.1).to_equal(true)
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea6d27355c79c9433311b0cdf4f56fcd9ad4c6807f433737041e9b518a0fd86d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea6d27355c79c9433311b0cdf4f56fcd9ad4c6807f433737041e9b518a0fd86d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea6d27355c79c9433311b0cdf4f56fcd9ad4c6807f433737041e9b518a0fd86d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/rendering/empty_block_margin_self_collapse_spec.spl
mirror: doc/06_spec/02_integration/rendering/empty_block_margin_self_collapse_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/empty_block_margin_self_collapse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/empty_block_margin_self_collapse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/empty_block_margin_self_collapse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/empty_block_margin_self_collapse_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders an empty margined block as contributing no extra vertical space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/empty_block_margin_self_collapse_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses a run of empty blocks the same as one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/empty_block_margin_self_collapse_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not self-collapse an empty block with padding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
