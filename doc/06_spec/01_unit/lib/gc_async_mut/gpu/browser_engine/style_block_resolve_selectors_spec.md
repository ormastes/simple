# Style Block Resolve Selectors Specification

> Tests covering style_block_resolve selector entry points, style_block_resolve child combinator, style_block_resolve structural pseudo-classes, style_block_resolve :empty, style_block_resolve :nth-child formulas, style_block_resolve :where compound, style_block_resolve attribute selectors, style_block_resolve attribute operators, style_block_resolve functional selector lists.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style Block Resolve Selectors Specification

## Scenarios

### style_block_resolve selector entry points

#### rejects an empty selector

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an empty selector
   - Expected: selector_matches("", el("div"), nil, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty selector")
expect(selector_matches("", el("div"), nil, 1, 1)).to_equal(false)
```

</details>

#### rejects an empty simple selector

- rejects an empty simple selector
   - Expected: simple_selector_matches("", el("div"), 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty simple selector")
expect(simple_selector_matches("", el("div"), 1, 1)).to_equal(false)
```

</details>

### style_block_resolve child combinator

#### matches a child combinator only when the parent is the immediate parent

- matches a child combinator only when the parent is the immediate parent
   - Expected: selector_matches("div > span", el("span"), el("p"), 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches a child combinator only when the parent is the immediate parent")
expect(selector_matches("div > span", el("span"), el("p"), 1, 1)).to_equal(false)
```

</details>

#### matches a child combinator when the parent does match

- matches a child combinator when the parent does match
   - Expected: selector_matches("div > span", el("span"), el("div"), 1, 1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches a child combinator when the parent does match")
expect(selector_matches("div > span", el("span"), el("div"), 1, 1)).to_equal(true)
```

</details>

#### distinguishes the child combinator from the descendant combinator

- distinguishes the child combinator from the descendant combinator
   - Expected: selector_matches("div > span", span, p, 1, 1) is false
   - Expected: selector_matches("div span", span, p, 1, 1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes the child combinator from the descendant combinator")
# Identical node and parent; only the combinator differs. Under the
# fall-through defect both answered true.
val span = el("span")
val p = el("p")
expect(selector_matches("div > span", span, p, 1, 1)).to_equal(false)
expect(selector_matches("div span", span, p, 1, 1)).to_equal(true)
```

</details>

#### rejects when the right-hand side does not match the node

- rejects when the right-hand side does not match the node
   - Expected: selector_matches("div > span", div, div, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when the right-hand side does not match the node")
# Returns before the `match parent`, so this example is unaffected.
val div = el("div")
expect(selector_matches("div > span", div, div, 1, 1)).to_equal(false)
```

</details>

#### rejects when there is no parent to match against

- rejects when there is no parent to match against
   - Expected: selector_matches("div > span", el("span"), nil, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when there is no parent to match against")
# The `case None` arm is correct on both engines.
expect(selector_matches("div > span", el("span"), nil, 1, 1)).to_equal(false)
```

</details>

### style_block_resolve structural pseudo-classes

#### matches :last-child on the final sibling only

- matches :last-child on the final sibling only
   - Expected: simple_selector_matches(":last-child", el("div"), 3, 3) is true
   - Expected: simple_selector_matches(":last-child", el("div"), 2, 3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches :last-child on the final sibling only")
expect(simple_selector_matches(":last-child", el("div"), 3, 3)).to_equal(true)
expect(simple_selector_matches(":last-child", el("div"), 2, 3)).to_equal(false)
```

</details>

#### matches :only-child on a lone child

- matches :only-child on a lone child
   - Expected: simple_selector_matches(":only-child", el("div"), 1, 1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches :only-child on a lone child")
expect(simple_selector_matches(":only-child", el("div"), 1, 1)).to_equal(true)
```

</details>

#### matches a bare :nth-child with no compound base

- matches a bare :nth-child with no compound base
   - Expected: simple_selector_matches(":nth-child(2)", el("div"), 2, 4) is true
   - Expected: simple_selector_matches(":nth-child(2)", el("div"), 3, 4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches a bare :nth-child with no compound base")
expect(simple_selector_matches(":nth-child(2)", el("div"), 2, 4)).to_equal(true)
expect(simple_selector_matches(":nth-child(2)", el("div"), 3, 4)).to_equal(false)
```

</details>

#### rejects a structural pseudo that is not at the end of the selector

- rejects a structural pseudo that is not at the end of the selector
   - Expected: simple_selector_matches("div:emptyx", el("div"), 1, 1) is false
   - Expected: simple_selector_matches("div:first-childx", el("div"), 1, 1) is false
   - Expected: simple_selector_matches("div:last-childx", el("div"), 1, 1) is false
   - Expected: simple_selector_matches("div:only-childx", el("div"), 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a structural pseudo that is not at the end of the selector")
# The `pos + len(pseudo) != sel.len()` guards: a trailing character
# after the pseudo makes the whole selector unmatchable.
expect(simple_selector_matches("div:emptyx", el("div"), 1, 1)).to_equal(false)
expect(simple_selector_matches("div:first-childx", el("div"), 1, 1)).to_equal(false)
expect(simple_selector_matches("div:last-childx", el("div"), 1, 1)).to_equal(false)
expect(simple_selector_matches("div:only-childx", el("div"), 1, 1)).to_equal(false)
```

</details>

### style_block_resolve :empty

#### matches an element with no children

- matches an element with no children
   - Expected: simple_selector_matches(":empty", el("div"), 1, 1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches an element with no children")
expect(simple_selector_matches(":empty", el("div"), 1, 1)).to_equal(true)
```

</details>

#### matches an element whose only child is whitespace text

- matches an element whose only child is whitespace text
   - Expected: simple_selector_matches(":empty", ws, 1, 1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches an element whose only child is whitespace text")
val ws = el_children("div", [BeDomNode.text_node(2, "   ")])
expect(simple_selector_matches(":empty", ws, 1, 1)).to_equal(true)
```

</details>

#### rejects an element with an element child

- rejects an element with an element child
   - Expected: simple_selector_matches(":empty", parent, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an element with an element child")
val parent = el_children("div", [el("span")])
expect(simple_selector_matches(":empty", parent, 1, 1)).to_equal(false)
```

</details>

#### rejects an element with non-blank text

- rejects an element with non-blank text
   - Expected: simple_selector_matches(":empty", parent, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an element with non-blank text")
val parent = el_children("div", [BeDomNode.text_node(2, "hi")])
expect(simple_selector_matches(":empty", parent, 1, 1)).to_equal(false)
```

</details>

### style_block_resolve :nth-child formulas

#### matches the 2n formula on even positions

- matches the 2n formula on even positions
   - Expected: simple_selector_matches(":nth-child(2n)", el("div"), 4, 6) is true
   - Expected: simple_selector_matches(":nth-child(2n)", el("div"), 3, 6) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the 2n formula on even positions")
expect(simple_selector_matches(":nth-child(2n)", el("div"), 4, 6)).to_equal(true)
expect(simple_selector_matches(":nth-child(2n)", el("div"), 3, 6)).to_equal(false)
```

</details>

#### matches the n+3 formula from the third position on

- matches the n+3 formula from the third position on
   - Expected: simple_selector_matches(":nth-child(n+3)", el("div"), 4, 6) is true
   - Expected: simple_selector_matches(":nth-child(n+3)", el("div"), 2, 6) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the n+3 formula from the third position on")
expect(simple_selector_matches(":nth-child(n+3)", el("div"), 4, 6)).to_equal(true)
expect(simple_selector_matches(":nth-child(n+3)", el("div"), 2, 6)).to_equal(false)
```

</details>

#### strips interior whitespace out of a formula

- strips interior whitespace out of a formula
   - Expected: simple_selector_matches(":nth-child(2n + 1)", el("div"), 3, 6) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips interior whitespace out of a formula")
# `2n + 1` must behave exactly like `2n+1`.
expect(simple_selector_matches(":nth-child(2n + 1)", el("div"), 3, 6)).to_equal(true)
```

</details>

### style_block_resolve :where compound

#### matches a tag compounded with :where

- matches a tag compounded with :where
   - Expected: simple_selector_matches("div:where(.hero)", divc, 1, 1) is true
   - Expected: simple_selector_matches("div:where(.other)", divc, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches a tag compounded with :where")
val divc = el_attrs("div", {"class": "hero"})
expect(simple_selector_matches("div:where(.hero)", divc, 1, 1)).to_equal(true)
expect(simple_selector_matches("div:where(.other)", divc, 1, 1)).to_equal(false)
```

</details>

### style_block_resolve attribute selectors

#### rejects an attribute selector with no closing bracket

- rejects an attribute selector with no closing bracket
   - Expected: simple_selector_matches("div[foo", el("div"), 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an attribute selector with no closing bracket")
expect(simple_selector_matches("div[foo", el("div"), 1, 1)).to_equal(false)
```

</details>

#### rejects :root on a non-html element and accepts it on html

- rejects :root on a non-html element and accepts it on html
   - Expected: simple_selector_matches(":root[lang]", el("div"), 1, 1) is false
   - Expected: simple_selector_matches(":root[lang]", html, 1, 1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects :root on a non-html element and accepts it on html")
val html = el_attrs("html", {"lang": "en-US"})
expect(simple_selector_matches(":root[lang]", el("div"), 1, 1)).to_equal(false)
expect(simple_selector_matches(":root[lang]", html, 1, 1)).to_equal(true)
```

</details>

#### rejects when the compound base before the bracket does not match

- rejects when the compound base before the bracket does not match
   - Expected: simple_selector_matches("span[lang]", html, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when the compound base before the bracket does not match")
val html = el_attrs("html", {"lang": "en-US"})
expect(simple_selector_matches("span[lang]", html, 1, 1)).to_equal(false)
```

</details>

#### rejects an empty attribute body

- rejects an empty attribute body
   - Expected: simple_selector_matches("div[]", el("div"), 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty attribute body")
expect(simple_selector_matches("div[]", el("div"), 1, 1)).to_equal(false)
```

</details>

#### rejects a valued attribute selector when the attribute is absent

- rejects a valued attribute selector when the attribute is absent
   - Expected: simple_selector_matches("div[data-x=y]", el("div"), 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a valued attribute selector when the attribute is absent")
expect(simple_selector_matches("div[data-x=y]", el("div"), 1, 1)).to_equal(false)
```

</details>

### style_block_resolve attribute operators

#### applies the i flag to a prefix match

- applies the i flag to a prefix match
   - Expected: simple_selector_matches("a[href^=\"http\" i]", a, 1, 1) is true
   - Expected: simple_selector_matches("a[href^=\"ftp\" i]", a, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies the i flag to a prefix match")
val a = el_attrs("a", {"href": "HTTP://Example.test/Docs"})
expect(simple_selector_matches("a[href^=\"http\" i]", a, 1, 1)).to_equal(true)
expect(simple_selector_matches("a[href^=\"ftp\" i]", a, 1, 1)).to_equal(false)
```

</details>

#### stays case-sensitive without the i flag

- stays case-sensitive without the i flag
   - Expected: simple_selector_matches("a[href^=\"HTTP\"]", a, 1, 1) is true
   - Expected: simple_selector_matches("a[href^=\"http\"]", a, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stays case-sensitive without the i flag")
val a = el_attrs("a", {"href": "HTTP://Example.test/Docs"})
expect(simple_selector_matches("a[href^=\"HTTP\"]", a, 1, 1)).to_equal(true)
expect(simple_selector_matches("a[href^=\"http\"]", a, 1, 1)).to_equal(false)
```

</details>

#### matches the hyphen-prefix operator on a language subtag

- matches the hyphen-prefix operator on a language subtag
   - Expected: simple_selector_matches("html[lang|=\"en\"]", html, 1, 1) is true
   - Expected: simple_selector_matches("html[lang|=\"en-US\"]", html, 1, 1) is true
   - Expected: simple_selector_matches("html[lang|=\"fr\"]", html, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the hyphen-prefix operator on a language subtag")
val html = el_attrs("html", {"lang": "en-US"})
expect(simple_selector_matches("html[lang|=\"en\"]", html, 1, 1)).to_equal(true)
expect(simple_selector_matches("html[lang|=\"en-US\"]", html, 1, 1)).to_equal(true)
expect(simple_selector_matches("html[lang|=\"fr\"]", html, 1, 1)).to_equal(false)
```

</details>

### style_block_resolve functional selector lists

#### rejects :is() whose parenthesis is never closed

- rejects :is() whose parenthesis is never closed
   - Expected: simple_selector_matches(":is(div", el("div"), 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects :is() whose parenthesis is never closed")
expect(simple_selector_matches(":is(div", el("div"), 1, 1)).to_equal(false)
```

</details>

#### rejects :not() whose parenthesis is never closed

- rejects :not() whose parenthesis is never closed
   - Expected: simple_selector_matches(":not(div", el("div"), 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects :not() whose parenthesis is never closed")
expect(simple_selector_matches(":not(div", el("div"), 1, 1)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_resolve_selectors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering style_block_resolve selector entry points, style_block_resolve child combinator, style_block_resolve structural pseudo-classes, style_block_resolve :empty, style_block_resolve :nth-child formulas, style_block_resolve :where compound, style_block_resolve attribute selectors, style_block_resolve attribute operators, style_block_resolve functional selector lists.
- style_block_resolve selector entry points
- style_block_resolve child combinator
- style_block_resolve structural pseudo-classes
- style_block_resolve :empty
- style_block_resolve :nth-child formulas
- style_block_resolve :where compound
- style_block_resolve attribute selectors
- style_block_resolve attribute operators
- style_block_resolve functional selector lists

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `ab0a0cbca04cdad2c01f0b05cdbd8f2f0c75d9d407db43c0c09a05f9664a31a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab0a0cbca04cdad2c01f0b05cdbd8f2f0c75d9d407db43c0c09a05f9664a31a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab0a0cbca04cdad2c01f0b05cdbd8f2f0c75d9d407db43c0c09a05f9664a31a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_resolve_selectors_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_resolve_selectors_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_resolve_selectors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_resolve_selectors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_resolve_selectors_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an empty selector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_resolve_selectors_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an empty simple selector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_resolve_selectors_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches a child combinator only when the parent is the immediate parent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
