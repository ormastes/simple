# Convert Storage Multibyte Specification

> Tests covering storage_to_markdown / markdown_to_storage multi-byte.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Convert Storage Multibyte Specification

## Scenarios

### storage_to_markdown / markdown_to_storage multi-byte

#### café before a tag does not crash and converts identically to the ASCII case

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- café before a tag does not crash and converts identically to the ASCII case
   - Expected: with_multibyte equals `café text\n\n# Title`
   - Expected: ascii_only equals `plain text\n\n# Title`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("café before a tag does not crash and converts identically to the ASCII case")
val with_multibyte = storage_to_markdown("<p>café text</p><h1>Title</h1>")
val ascii_only = storage_to_markdown("<p>plain text</p><h1>Title</h1>")
expect(with_multibyte).to_equal("café text\n\n# Title")
expect(ascii_only).to_equal("plain text\n\n# Title")
```

</details>

#### CJK content before a tag converts correctly

- CJK content before a tag converts correctly
   - Expected: out equals `日本語\n\n## 見出し`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CJK content before a tag converts correctly")
val out = storage_to_markdown("<p>日本語</p><h2>見出し</h2>")
expect(out).to_equal("日本語\n\n## 見出し")
```

</details>

#### em-dash inside tag content does not desync subsequent tag boundaries

- em-dash inside tag content does not desync subsequent tag boundaries
   - Expected: out equals `a—b\n\n**bold**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("em-dash inside tag content does not desync subsequent tag boundaries")
val out = storage_to_markdown("<p>a—b</p><strong>bold</strong>")
expect(out).to_equal("a—b\n\n**bold**")
```

</details>

#### multiple multi-byte characters before a closing tag

- multiple multi-byte characters before a closing tag
   - Expected: out equals `*café日本語—end*done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple multi-byte characters before a closing tag")
val out = storage_to_markdown("<em>café日本語—end</em><p>done</p>")
expect(out).to_equal("*café日本語—end*done")
```

</details>

#### pure ASCII is unaffected (regression guard)

- pure ASCII is unaffected (regression guard)
   - Expected: out equals `# Title\n\nBody **bold** text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pure ASCII is unaffected (regression guard)")
val out = storage_to_markdown("<h1>Title</h1><p>Body <strong>bold</strong> text</p>")
expect(out).to_equal("# Title\n\nBody **bold** text")
```

</details>

#### markdown_to_storage: multi-byte content inside a paired marker (bold) is not corrupted

- markdown_to_storage: multi-byte content inside a paired marker (bold) is not corrupted
   - Expected: out equals `<p>Body <strong>bold café</strong> text</p>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("markdown_to_storage: multi-byte content inside a paired marker (bold) is not corrupted")
val out = markdown_to_storage("Body **bold café** text")
expect(out).to_equal("<p>Body <strong>bold café</strong> text</p>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/convert_storage_multibyte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering storage_to_markdown / markdown_to_storage multi-byte.
- storage_to_markdown / markdown_to_storage multi-byte

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

- Canonical SPipe generation for source `458fbf82457e4a69ef18b62bf8aeeea2b4c97ccd37559d4eb649b4bc497c3ef4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `458fbf82457e4a69ef18b62bf8aeeea2b4c97ccd37559d4eb649b4bc497c3ef4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `458fbf82457e4a69ef18b62bf8aeeea2b4c97ccd37559d4eb649b4bc497c3ef4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/devhub/convert_storage_multibyte_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/convert_storage_multibyte_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/convert_storage_multibyte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/convert_storage_multibyte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/convert_storage_multibyte_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'café before a tag does not crash and converts identically to the ASCII case' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/convert_storage_multibyte_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CJK content before a tag converts correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/convert_storage_multibyte_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'em-dash inside tag content does not desync subsequent tag boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
