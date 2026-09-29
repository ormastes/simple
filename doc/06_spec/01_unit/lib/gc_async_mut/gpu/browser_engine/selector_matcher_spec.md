# Selector Matcher Specification

> Tests covering browser engine selector matcher.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

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

#### rejects :not with a compound class written in single quotes

- rejects :not with a compound class written in single quotes
   - Expected: br_selector_list_contains_not_self("button:not(button.primary)", "button", tag) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects :not with a compound class written in single quotes")
val tag = "button class='primary'"
expect(br_selector_list_contains_not_self("button:not(button.primary)", "button", tag)).to_equal(false)
```

</details>

#### matches :not when the single-quoted class differs

- matches :not when the single-quoted class differs
   - Expected: br_selector_list_contains_not_self("button:not(button.primary)", "button", tag) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches :not when the single-quoted class differs")
val tag = "button class='secondary'"
expect(br_selector_list_contains_not_self("button:not(button.primary)", "button", tag)).to_equal(true)
```

</details>

#### treats an unterminated single-quoted attribute as absent

- treats an unterminated single-quoted attribute as absent
   - Expected: br_selector_list_contains_not_self("button:not(button.primary)", "button", tag) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats an unterminated single-quoted attribute as absent")
# No closing quote, so the `close >= 0` guard fails and the option
# cannot match -- the element stays a valid :not() match.
val tag = "button class='primary"
expect(br_selector_list_contains_not_self("button:not(button.primary)", "button", tag)).to_equal(true)
```

</details>

#### reports no tag name for markup with an empty tag body

- reports no tag name for markup with an empty tag body
   - Expected: br_tag_name_from_content("<>") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no tag name for markup with an empty tag body")
expect(br_tag_name_from_content("<>")).to_equal("")
```

</details>

#### reports the tag name for ordinary markup

- reports the tag name for ordinary markup
   - Expected: br_tag_name_from_content("<a>") equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the tag name for ordinary markup")
expect(br_tag_name_from_content("<a>")).to_equal("a")
```

</details>

#### rejects a selector that never names the element with :not

- rejects a selector that never names the element with :not
   - Expected: br_selector_list_contains_not_self("p.foo", "a", "a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a selector that never names the element with :not")
expect(br_selector_list_contains_not_self("p.foo", "a", "a")).to_equal(false)
```

</details>

#### rejects a :not selector whose parenthesis is never closed

- rejects a :not selector whose parenthesis is never closed
   - Expected: br_selector_list_contains_not_self("a:not(b", "a", "a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a :not selector whose parenthesis is never closed")
expect(br_selector_list_contains_not_self("a:not(b", "a", "a")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering browser engine selector matcher.
- browser engine selector matcher

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `ac04803675f97c8c62c145350b182592bf9376ea3afeb1cd15f9c2be53dd664f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac04803675f97c8c62c145350b182592bf9376ea3afeb1cd15f9c2be53dd664f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac04803675f97c8c62c145350b182592bf9376ea3afeb1cd15f9c2be53dd664f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches :not when an attribute substring option is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects :not when an attribute substring option is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches :not with compound class options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
