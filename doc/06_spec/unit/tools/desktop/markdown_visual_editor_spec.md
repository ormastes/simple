# Markdown Visual Editor Specification

> Tests covering markdown visual editor model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown Visual Editor Specification

## Scenarios

### markdown visual editor model

#### recognizes markdown paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes markdown paths
   - Expected: markdown_visual_is_markdown_path("/home/notes/os.md") is true
   - Expected: markdown_visual_is_markdown_path("/home/notes/os.txt") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes markdown paths")
expect(markdown_visual_is_markdown_path("/home/notes/os.md")).to_equal(true)
expect(markdown_visual_is_markdown_path("/home/notes/os.txt")).to_equal(false)
```

</details>

#### uses the first heading as the note title

- uses the first heading as the note title
   - Expected: markdown_visual_title("/home/notes/os.md", "# SimpleOS\nbody") equals `SimpleOS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the first heading as the note title")
expect(markdown_visual_title("/home/notes/os.md", "# SimpleOS\nbody")).to_equal("SimpleOS")
```

</details>

#### falls back to the file basename

- falls back to the file basename
   - Expected: markdown_visual_title("/home/notes/os.md", "body") equals `os`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to the file basename")
expect(markdown_visual_title("/home/notes/os.md", "body")).to_equal("os")
```

</details>

#### extracts visual blocks and preview lines

- extracts visual blocks and preview lines
   - Expected: blocks[0].kind equals `heading`
   - Expected: blocks[1].kind equals `bullet`
   - Expected: rows[0] equals `Title`
   - Expected: rows[1] equals `* task`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts visual blocks and preview lines")
val blocks = markdown_visual_blocks("# Title\n- task")
val rows = markdown_visual_preview_lines("# Title\n- task")

expect(blocks[0].kind).to_equal("heading")
expect(blocks[1].kind).to_equal("bullet")
expect(rows[0]).to_equal("Title")
expect(rows[1]).to_equal("* task")
```

</details>

#### extracts wiki links

- extracts wiki links


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts wiki links")
val links = markdown_visual_wiki_links("See [[Kernel]] and [[Packages]].")

expect(links).to_contain("Kernel")
expect(links).to_contain("Packages")
```

</details>

#### creates a complete visual note

- creates a complete visual note
   - Expected: note.title equals `OS`
   - Expected: note.wiki_links[0] equals `Kernel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a complete visual note")
val note = markdown_visual_note("/home/notes/os.md", "# OS\nSee [[Kernel]].")

expect(note.title).to_equal("OS")
expect(note.wiki_links[0]).to_equal("Kernel")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/desktop/markdown_visual_editor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering markdown visual editor model.
- markdown visual editor model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `7c794f598d46e3a038ad2e271814bee64cb5209652ba1d270f2e872e4fb88ab3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c794f598d46e3a038ad2e271814bee64cb5209652ba1d270f2e872e4fb88ab3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c794f598d46e3a038ad2e271814bee64cb5209652ba1d270f2e872e4fb88ab3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/tools/desktop/markdown_visual_editor_spec.spl
mirror: doc/06_spec/unit/tools/desktop/markdown_visual_editor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/desktop/markdown_visual_editor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/desktop/markdown_visual_editor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/desktop/markdown_visual_editor_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes markdown paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/desktop/markdown_visual_editor_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the first heading as the note title' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/desktop/markdown_visual_editor_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to the file basename' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
