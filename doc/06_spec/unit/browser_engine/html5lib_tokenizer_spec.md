# Html5lib Tokenizer Specification

> Tests covering html5lib tokenizer test vectors, 132-corpus regression gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html5lib Tokenizer Specification

## Scenarios

### html5lib tokenizer test vectors

#### AC-6: test/fixtures/html5lib/test1.json fixture file exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-6: test/fixtures/html5lib/test1.json fixture file exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: test/fixtures/html5lib/test1.json fixture file exists")
val content = _load_fixture("test1.json")
expect(content.len()).to_be_greater_than(0)
```

</details>

#### AC-6: test1.json contains at least one test vector

- AC-6: test1.json contains at least one test vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: test1.json contains at least one test vector")
val content = _load_fixture("test1.json")
val count = _count_vectors_in_json(content)
expect(count).to_be_greater_than(0)
```

</details>

#### AC-6: test1.json pass rate is at least 90 percent

- AC-6: test1.json pass rate is at least 90 percent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: test1.json pass rate is at least 90 percent")
val rate = _pass_rate_for_fixture("test1.json")
expect(rate).to_be_greater_than(89)
```

</details>

#### AC-6: test2.json pass rate is at least 90 percent

- AC-6: test2.json pass rate is at least 90 percent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: test2.json pass rate is at least 90 percent")
val rate = _pass_rate_for_fixture("test2.json")
expect(rate).to_be_greater_than(89)
```

</details>

### 132-corpus regression gate

#### AC-7: corpus baseline directory exists

- AC-7: corpus baseline directory exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: corpus baseline directory exists")
val content = read_file_text("test/baselines/famous_site_corpus/site_0/baseline.txt")
expect(content.len()).to_be_greater_than(-1)
```

</details>

#### AC-7: html tree builder produces a document node from minimal HTML

- AC-7: html tree builder produces a document node from minimal HTML
   - Expected: tag equals `#document`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: html tree builder produces a document node from minimal HTML")
val tag = _parse_html_doc_tag("<html><body></body></html>")
expect(tag).to_equal("#document")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/browser_engine/html5lib_tokenizer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering html5lib tokenizer test vectors, 132-corpus regression gate.
- html5lib tokenizer test vectors
- 132-corpus regression gate

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

- Canonical SPipe generation for source `25237a054fceaedb3bf8722b417fb6ad9f3124b10440ddd618289f1f7b5289af`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `25237a054fceaedb3bf8722b417fb6ad9f3124b10440ddd618289f1f7b5289af`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `25237a054fceaedb3bf8722b417fb6ad9f3124b10440ddd618289f1f7b5289af`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/browser_engine/html5lib_tokenizer_spec.spl
mirror: doc/06_spec/unit/browser_engine/html5lib_tokenizer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser_engine/html5lib_tokenizer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser_engine/html5lib_tokenizer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser_engine/html5lib_tokenizer_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: test/fixtures/html5lib/test1.json fixture file exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/html5lib_tokenizer_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: test1.json contains at least one test vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/html5lib_tokenizer_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: test1.json pass rate is at least 90 percent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
