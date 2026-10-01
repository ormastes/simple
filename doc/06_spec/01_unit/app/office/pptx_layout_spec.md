# pptx_layout_spec

> PPTX bullet levels and slide layout variants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pptx_layout_spec

PPTX bullet levels and slide layout variants.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/pptx_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

PPTX bullet levels and slide layout variants.

Nested deck bullets export as `<a:pPr lvl=\"N\"><a:buChar/></a:pPr>` paragraph
properties (lvl omitted for level 0) and import back to indentation;
@layout: title-only|section map to alternate shape arrangements (centered
title / big centered title with a larger font size attr) marked by shape
names, round-tripping losslessly. Package integrity is validated with the
system `unzip -t`.

Lives in its own spec file (not pptx_export_spec.spl) because that file's
9 package-building cases already run ~60s and the test runner terminates a
file at its per-file budget — added cases there were killed mid-run.

## Scenarios

### PPTX: bullet levels and slide layouts

#### exports bullet lvl attrs and layout arrangements (3-slide ground truth)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports bullet lvl attrs and layout arrangements (3-slide ground truth)
   - Expected: texts2.len() equals `1`
   - Expected: texts2[0] equals `Break Time`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exports bullet lvl attrs and layout arrangements (3-slide ground truth)")
val src = "Agenda\n- Opening\n  - Welcome note\n    - Speaker intro\n- Closing\nPlain wrap-up line\n@notes: pace slowly\n---\nBreak Time\n@layout: title-only\n---\nPart Two\n@layout: section\n@transition: fade"
val deck = parse_deck(src)
val pptx = deck_to_pptx_bytes(deck)
# Slide 1 (default layout): nested bullet levels, lvl omitted for 0
val slide1 = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide1).to_contain("lvl=\"1\"")
expect(slide1).to_contain("lvl=\"2\"")
expect(slide1.contains("lvl=\"0\"")).to_be(false)
expect(slide1).to_contain("<a:pPr><a:buChar char=\"-\"/></a:pPr>")
# Title and plain body paragraphs carry no bullet properties
expect(slide1).to_contain("<a:p><a:r><a:t>Agenda</a:t>")
expect(slide1).to_contain("<a:p><a:r><a:t>Plain wrap-up line</a:t>")
# Slide 2: title-only = just a centered title shape
val slide2 = zip_extract_text(pptx, "ppt/slides/slide2.xml")
expect(slide2).to_contain("name=\"ctrTitle\"")
val texts2 = pptx_slide_texts(slide2)
expect(texts2.len()).to_equal(1)
expect(texts2[0]).to_equal("Break Time")
# Slide 3: section = big centered title with larger font size attr
val slide3 = zip_extract_text(pptx, "ppt/slides/slide3.xml")
expect(slide3).to_contain("name=\"sectionTitle\"")
expect(slide3).to_contain("<a:rPr sz=\"4400\"/>")
```

</details>

#### round-trips levels and layouts losslessly and passes system unzip -t

- round-trips levels and layouts losslessly and passes system unzip -t
   - Expected: deck_to_text(deck) equals `src`
   - Expected: deck2.len() equals `3`
   - Expected: deck_to_text(deck2) equals `src`
   - Expected: deck2[0].notes equals `pace slowly`
   - Expected: deck2[2].transition equals `fade`
   - Expected: test_result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("round-trips levels and layouts losslessly and passes system unzip -t")
val src = "Agenda\n- Opening\n  - Welcome note\n    - Speaker intro\n- Closing\nPlain wrap-up line\n@notes: pace slowly\n---\nBreak Time\n@layout: title-only\n---\nPart Two\n@layout: section\n@transition: fade"
val deck = parse_deck(src)
expect(deck_to_text(deck)).to_equal(src)
val pptx = deck_to_pptx_bytes(deck)
val deck2 = pptx_bytes_to_deck(pptx)
expect(deck2.len()).to_equal(3)
expect(deck_to_text(deck2)).to_equal(src)
expect(deck2[0].notes).to_equal("pace slowly")
expect(deck2[2].transition).to_equal("fade")
val out_path = "/tmp/claude-1000/-home-ormastes-dev-pub-simple/de80534b-2c68-466d-a211-9ec2529fed18/scratchpad/pptx_bullets_spec.pptx"
File.write_bytes(out_path, pptx)
val test_result = run("unzip", ["-t", out_path])
expect(test_result.exit_code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `76e81dd93a1ebafd9336a9370c5fb2985679835265a0f7305ad73d9fc709aebb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `76e81dd93a1ebafd9336a9370c5fb2985679835265a0f7305ad73d9fc709aebb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `76e81dd93a1ebafd9336a9370c5fb2985679835265a0f7305ad73d9fc709aebb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/office/pptx_layout_spec.spl
mirror: doc/06_spec/01_unit/app/office/pptx_layout_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/pptx_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/pptx_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/pptx_layout_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/pptx_layout_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports bullet lvl attrs and layout arrangements (3-slide ground truth)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/pptx_layout_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips levels and layouts losslessly and passes system unzip -t' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
