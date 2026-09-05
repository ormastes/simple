# File Specification

> Tests covering file tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Specification

## Scenarios

### file tool

#### extension detection

#### identifies .spl as Simple source

- identifies .spl as Simple source
   - Expected: is_spl is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies .spl as Simple source")
val name = "main.spl"
val is_spl = name.ends_with(".spl")
expect(is_spl).to_equal(true)
```

</details>

#### identifies .shs as Simple shell

- identifies .shs as Simple shell
   - Expected: is_shs is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies .shs as Simple shell")
val name = "build.shs"
val is_shs = name.ends_with(".shs")
expect(is_shs).to_equal(true)
```

</details>

#### identifies .md as Markdown

- identifies .md as Markdown
   - Expected: is_md is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies .md as Markdown")
val name = "README.md"
val is_md = name.ends_with(".md")
expect(is_md).to_equal(true)
```

</details>

#### content inspection

#### detects shebang scripts

- detects shebang scripts
   - Expected: content.starts_with("#!") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects shebang scripts")
val content = "#!/bin/sh\necho hello"
expect(content.starts_with("#!")).to_equal(true)
```

</details>

#### detects JSON by opening brace

- detects JSON by opening brace
   - Expected: content.starts_with("{") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects JSON by opening brace")
val content = "{\"key\": \"value\"}"
expect(content.starts_with("{")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/shell/file_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering file tool.
- file tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `2b99a479cdc08babe582ac35f823f2875a543d46bffea57739b51c045bbb3d5e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b99a479cdc08babe582ac35f823f2875a543d46bffea57739b51c045bbb3d5e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b99a479cdc08babe582ac35f823f2875a543d46bffea57739b51c045bbb3d5e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/tools/shell/file_spec.spl
mirror: doc/06_spec/unit/tools/shell/file_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/shell/file_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/shell/file_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/shell/file_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies .spl as Simple source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/file_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies .shs as Simple shell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/file_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies .md as Markdown' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
