# Md Wiki Transclusion Heading Specification

> Tests covering heading-scoped transclusion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Wiki Transclusion Heading Specification

## Scenarios

### heading-scoped transclusion

#### anchored target embeds only the matching heading section

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- anchored target embeds only the matching heading section
   - Expected: sec equals `## Alpha\nalpha body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("anchored target embeds only the matching heading section")
val docs = [md_wiki_document("notes/target.md", "# Target\nintro\n## Alpha\nalpha body\n## Beta\nbeta body")]
val idx = md_wiki_index_documents(docs)
val sec = md_wiki_transclusion_content(idx, "Target#Alpha")
expect(sec).to_equal("## Alpha\nalpha body")
```

</details>

#### section includes deeper subheadings until a same-level heading

- section includes deeper subheadings until a same-level heading
   - Expected: sec equals `## Alpha\nbody\n### Sub\nsub body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("section includes deeper subheadings until a same-level heading")
val body = "## Alpha\nbody\n### Sub\nsub body\n## Beta\nbeta"
val sec = md_wiki_heading_section(body, "Alpha")
expect(sec).to_equal("## Alpha\nbody\n### Sub\nsub body")
```

</details>

#### section of the last heading runs to end of note

- section of the last heading runs to end of note
   - Expected: sec equals `## Last\nfinal body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("section of the last heading runs to end of note")
val sec = md_wiki_heading_section("# A\nx\n## Last\nfinal body", "Last")
expect(sec).to_equal("## Last\nfinal body")
```

</details>

#### unknown anchor returns empty

- unknown anchor returns empty
   - Expected: sec.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unknown anchor returns empty")
val docs = [md_wiki_document("notes/target.md", "# Target\nintro")]
val idx = md_wiki_index_documents(docs)
val sec = md_wiki_transclusion_content(idx, "Target#Nothing")
expect(sec.len()).to_equal(0)
```

</details>

#### plain target still returns the whole note

- plain target still returns the whole note
   - Expected: full.len() > 0 is true
   - Expected: full.index_of("alpha body") >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("plain target still returns the whole note")
val docs = [md_wiki_document("notes/target.md", "# Target\nintro\n## Alpha\nalpha body")]
val idx = md_wiki_index_documents(docs)
val full = md_wiki_transclusion_content(idx, "Target")
expect(full.len() > 0).to_equal(true)
expect(full.index_of("alpha body") >= 0).to_equal(true)
```

</details>

#### anchored target on a missing note returns empty

- anchored target on a missing note returns empty
   - Expected: sec.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("anchored target on a missing note returns empty")
val docs = [md_wiki_document("notes/other.md", "# Other\nbody")]
val idx = md_wiki_index_documents(docs)
val sec = md_wiki_transclusion_content(idx, "Missing#Alpha")
expect(sec.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/services/md_wiki_transclusion_heading_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering heading-scoped transclusion.
- heading-scoped transclusion

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b62204ced5b45d20a101e47a2bcbb2dcacaac1446799bca3d2dac8329dc22278`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b62204ced5b45d20a101e47a2bcbb2dcacaac1446799bca3d2dac8329dc22278`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b62204ced5b45d20a101e47a2bcbb2dcacaac1446799bca3d2dac8329dc22278`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/editor/services/md_wiki_transclusion_heading_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/services/md_wiki_transclusion_heading_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/services/md_wiki_transclusion_heading_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/services/md_wiki_transclusion_heading_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/services/md_wiki_transclusion_heading_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/editor/services/md_wiki_transclusion_heading_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'anchored target embeds only the matching heading section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/services/md_wiki_transclusion_heading_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'section includes deeper subheadings until a same-level heading' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/services/md_wiki_transclusion_heading_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'section of the last heading runs to end of note' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
