# Claude Full display tags

> Pure Simple coverage for display-title XML tag stripping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full display tags

Pure Simple coverage for display-title XML tag stripping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/display_tags_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for display-title XML tag stripping.

## Scenarios

### Claude full display tags

#### strips lowercase XML-like tag blocks from display titles

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- strips lowercase XML-like tag blocks from display titles
- Check generic tag stripping
   - Expected: stripDisplayTags("hello <task>hidden</task> world") equals `hello  world`
   - Expected: stripDisplayTags("<hook-output a=\"b\">hidden</hook-output>\nvisible") equals `visible`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("strips lowercase XML-like tag blocks from display titles")
step("Check generic tag stripping")
expect(stripDisplayTags("hello <task>hidden</task> world")).to_equal("hello  world")
expect(stripDisplayTags("<hook-output a=\"b\">hidden</hook-output>\nvisible")).to_equal("visible")
```

</details>

#### keeps original text when generic stripping would empty it

- keeps original text when generic stripping would empty it
- Check fallback
   - Expected: stripDisplayTags("<task>hidden</task>") equals `<task>hidden</task>`
   - Expected: stripDisplayTagsAllowEmpty("<task>hidden</task>") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps original text when generic stripping would empty it")
step("Check fallback")
expect(stripDisplayTags("<task>hidden</task>")).to_equal("<task>hidden</task>")
expect(stripDisplayTagsAllowEmpty("<task>hidden</task>")).to_equal("")
```

</details>

#### preserves uppercase or unmatched angle text

- preserves uppercase or unmatched angle text
- Check user prose
   - Expected: stripDisplayTags("fix <Button> layout") equals `fix <Button> layout`
   - Expected: stripDisplayTags("when x < y") equals `when x < y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves uppercase or unmatched angle text")
step("Check user prose")
expect(stripDisplayTags("fix <Button> layout")).to_equal("fix <Button> layout")
expect(stripDisplayTags("when x < y")).to_equal("when x < y")
```

</details>

#### strips only IDE context tags for resubmit text

- strips only IDE context tags for resubmit text
- Check IDE-only stripping
   - Expected: stripIdeContextTags(textValue) equals `<code>keep</code>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("strips only IDE context tags for resubmit text")
step("Check IDE-only stripping")
val textValue = "<ide_opened_file>x</ide_opened_file><code>keep</code><ide_selection>y</ide_selection>"
expect(stripIdeContextTags(textValue)).to_equal("<code>keep</code>")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1367e27186793ad0076d4aca5cb1120fea4a35596c596b14b17b9757108dd1eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1367e27186793ad0076d4aca5cb1120fea4a35596c596b14b17b9757108dd1eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1367e27186793ad0076d4aca5cb1120fea4a35596c596b14b17b9757108dd1eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/display_tags_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/display_tags_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/display_tags_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/display_tags_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/display_tags_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips lowercase XML-like tag blocks from display titles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/display_tags_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps original text when generic stripping would empty it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/display_tags_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves uppercase or unmatched angle text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
