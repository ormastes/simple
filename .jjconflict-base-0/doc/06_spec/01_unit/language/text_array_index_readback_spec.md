# Text Array Index Readback Specification

> Tests covering module-level [text] array write-then-read-back.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Array Index Readback Specification

## Scenarios

### module-level [text] array write-then-read-back

#### direct inline push+index-read agrees (positive control)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- direct inline push+index-read agrees (positive control)
   - Expected: _direct_keys.len() equals `1`
   - Expected: _direct_keys[0] equals `hello`
   - Expected: _direct_keys[0].len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("direct inline push+index-read agrees (positive control)")
_direct_keys.push("hello")
expect(_direct_keys.len()).to_equal(1)
expect(_direct_keys[0]).to_equal("hello")
expect(_direct_keys[0].len()).to_equal(5)
```

</details>

#### push via a free function is visible to the caller ([text])

- push via a free function is visible to the caller ([text])
   - Expected: _indirect_keys.len() equals `1`
   - Expected: _indirect_keys[0] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("push via a free function is visible to the caller ([text])")
_store_text("hello")
expect(_indirect_keys.len()).to_equal(1)
expect(_indirect_keys[0]).to_equal("hello")
```

</details>

#### push via a free function is visible to the caller ([i64], not text-specific)

- push via a free function is visible to the caller ([i64], not text-specific)
   - Expected: _indirect_nums.len() equals `1`
   - Expected: _indirect_nums[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("push via a free function is visible to the caller ([i64], not text-specific)")
_store_num(42)
expect(_indirect_nums.len()).to_equal(1)
expect(_indirect_nums[0]).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/text_array_index_readback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering module-level [text] array write-then-read-back.
- module-level [text] array write-then-read-back

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

- `REQ-SSPEC-LANGUAGE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ff058039bdaf4f71c7fa57a3a999603c9d2c1c6d2c01ab110749858797d275ed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ff058039bdaf4f71c7fa57a3a999603c9d2c1c6d2c01ab110749858797d275ed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ff058039bdaf4f71c7fa57a3a999603c9d2c1c6d2c01ab110749858797d275ed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/language/text_array_index_readback_spec.spl
mirror: doc/06_spec/01_unit/language/text_array_index_readback_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/text_array_index_readback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/text_array_index_readback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/text_array_index_readback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/language/text_array_index_readback_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'direct inline push+index-read agrees (positive control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/text_array_index_readback_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'push via a free function is visible to the caller ([text])' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/text_array_index_readback_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'push via a free function is visible to the caller ([i64], not text-specific)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
