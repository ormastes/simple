# Selector Matcher Specification

> Tests covering browser engine selector matcher.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Selector Matcher Specification

## Scenarios

### browser engine selector matcher

#### matches :not when an attribute substring option is absent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches :not when an attribute substring option is absent
   - Expected: br_selector_list_contains_not_self("a:not([href*=\"admin\"])", "a", tag) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches :not when an attribute substring option is absent")
val tag = "a href=\"https://example.test/docs\" class=\"nav\""
expect(br_selector_list_contains_not_self("a:not([href*=\"admin\"])", "a", tag)).to_equal(true)
```

</details>

#### rejects :not when an attribute substring option is present

- rejects :not when an attribute substring option is present
   - Expected: br_selector_list_contains_not_self("a:not([href*=\"admin\"])", "a", tag) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects :not when an attribute substring option is present")
val tag = "a href=\"https://example.test/admin\" class=\"nav\""
expect(br_selector_list_contains_not_self("a:not([href*=\"admin\"])", "a", tag)).to_equal(false)
```

</details>

#### matches :not with compound class options

- matches :not with compound class options
   - Expected: br_selector_list_contains_not_self("button:not(button.primary)", "button", tag) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches :not with compound class options")
val tag = "button class=\"secondary\""
expect(br_selector_list_contains_not_self("button:not(button.primary)", "button", tag)).to_equal(true)
```

</details>

#### rejects :not with compound class options

- rejects :not with compound class options
   - Expected: br_selector_list_contains_not_self("button:not(button.primary)", "button", tag) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects :not with compound class options")
val tag = "button class=\"primary\""
expect(br_selector_list_contains_not_self("button:not(button.primary)", "button", tag)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering browser engine selector matcher.
- browser engine selector matcher

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7c752748e7899d3181fa455ac3840c424a09999fa2f6e7a694046197c0258a1c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c752748e7899d3181fa455ac3840c424a09999fa2f6e7a694046197c0258a1c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c752748e7899d3181fa455ac3840c424a09999fa2f6e7a694046197c0258a1c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches :not when an attribute substring option is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects :not when an attribute substring option is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches :not with compound class options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
