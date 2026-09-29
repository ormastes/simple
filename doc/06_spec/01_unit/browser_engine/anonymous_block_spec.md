# Anonymous Block Specification

> Tests covering Anonymous block generation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Anonymous Block Specification

## Scenarios

### Anonymous block generation

#### AC-3: wraps leading inline text before block sibling in anon block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-3: wraps leading inline text before block sibling in anon block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: wraps leading inline text before block sibling in anon block")
val box_ = _build_and_layout("<div>text<p>block</p></div>")
val anon_count = _count_anon_blocks(box_)
expect(anon_count).to_be_greater_than(0)
```

</details>

#### AC-3: wraps trailing inline text after block sibling in anon block

- AC-3: wraps trailing inline text after block sibling in anon block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: wraps trailing inline text after block sibling in anon block")
val box_ = _build_and_layout("<div><p>block</p>text after</div>")
val anon_count = _count_anon_blocks(box_)
expect(anon_count).to_be_greater_than(0)
```

</details>

#### AC-3: mixed inline and block children produce at least two layout children

- AC-3: mixed inline and block children produce at least two layout children


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: mixed inline and block children produce at least two layout children")
val box_ = _build_and_layout("<div>before<p>block</p>after</div>")
val count = _child_box_count(box_)
expect(count).to_be_greater_than(1)
```

</details>

#### AC-3: block-only children produce zero anonymous blocks

- AC-3: block-only children produce zero anonymous blocks
   - Expected: anon_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: block-only children produce zero anonymous blocks")
val box_ = _build_and_layout("<div><p>a</p><p>b</p></div>")
val anon_count = _count_anon_blocks(box_)
expect(anon_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/anonymous_block_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Anonymous block generation.
- Anonymous block generation

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

- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e03e3297842b2e32e2c4dfbfec366f1a48e4ca58fa870890aea1b12a382faad4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e03e3297842b2e32e2c4dfbfec366f1a48e4ca58fa870890aea1b12a382faad4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e03e3297842b2e32e2c4dfbfec366f1a48e4ca58fa870890aea1b12a382faad4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/browser_engine/anonymous_block_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/anonymous_block_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/anonymous_block_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/anonymous_block_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/anonymous_block_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/anonymous_block_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: wraps leading inline text before block sibling in anon block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/anonymous_block_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: wraps trailing inline text after block sibling in anon block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/anonymous_block_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: mixed inline and block children produce at least two layout children' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
