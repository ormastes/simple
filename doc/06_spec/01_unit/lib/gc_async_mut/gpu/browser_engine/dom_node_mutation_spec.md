# Dom Node Mutation Specification

> Tests covering BeDomNode attributes, BeDomNode children, BeDomNode inline style, BeDomNode event listeners, BeDomEvent default handling, BeDomNode manual tree dump.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dom Node Mutation Specification

## Scenarios

### BeDomNode attributes

#### stores an attribute and reads it back

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores an attribute and reads it back
   - Expected: n.get_attr("id") equals `hero`
   - Expected: n.has_attr("id") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores an attribute and reads it back")
var n = BeDomNode.element_with_id(1, "img")
n.set_attr("id", "hero")
expect(n.get_attr("id")).to_equal("hero")
expect(n.has_attr("id")).to_equal(true)
```

</details>

#### stores the three render-cache-invalidating attributes

- stores the three render-cache-invalidating attributes
   - Expected: n.get_attr("src") equals `a.png`
   - Expected: n.get_attr("poster") equals `p.png`
   - Expected: n.get_attr("style") equals `color:red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores the three render-cache-invalidating attributes")
# src / poster / style each drop a cached render key before storing.
var n = BeDomNode.element_with_id(1, "img")
n.set_attr("src", "a.png")
n.set_attr("poster", "p.png")
n.set_attr("style", "color:red")
expect(n.get_attr("src")).to_equal("a.png")
expect(n.get_attr("poster")).to_equal("p.png")
expect(n.get_attr("style")).to_equal("color:red")
```

</details>

#### removes a render-cache-invalidating attribute

- removes a render-cache-invalidating attribute
   - Expected: n.has_attr("src") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes a render-cache-invalidating attribute")
var n = BeDomNode.element_with_id(1, "img")
n.set_attr("src", "a.png")
n.remove_attr("src")
expect(n.has_attr("src")).to_equal(false)
```

</details>

#### removes a plain attribute

- removes a plain attribute
   - Expected: n.has_attr("id") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes a plain attribute")
var n = BeDomNode.element_with_id(1, "img")
n.set_attr("id", "hero")
n.remove_attr("id")
expect(n.has_attr("id")).to_equal(false)
```

</details>

### BeDomNode children

#### adopts a child and stamps its parent id

- adopts a child and stamps its parent id
   - Expected: parent.children.len() equals `1`
   - Expected: parent.children[0].parent_id equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("adopts a child and stamps its parent id")
var parent = BeDomNode.element_with_id(7, "div")
val kid = BeDomNode.element_with_id(8, "span")
parent.add_child(kid)
expect(parent.children.len()).to_equal(1)
expect(parent.children[0].parent_id).to_equal(7)
```

</details>

### BeDomNode inline style

#### sets every named inline style property

- sets every named inline style property
   - Expected: s.style.display equals `flex`
   - Expected: s.style.float_css equals `left`
   - Expected: s.style.clear_css equals `both`
   - Expected: s.style.overflow equals `hidden`
   - Expected: s.style.position equals `absolute`
   - Expected: s.style.color equals `red`
   - Expected: s.style.background_color equals `blue`
   - Expected: s.style.font_weight equals `bold`
   - Expected: s.style.text_align equals `center`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sets every named inline style property")
var s = BeDomNode.element_with_id(2, "p")
s.set_style("Display", " flex ")     # name lowered, value trimmed
s.set_style("float", "left")
s.set_style("clear", "both")
s.set_style("overflow", "hidden")
s.set_style("position", "absolute")
s.set_style("color", "red")
s.set_style("background-color", "blue")
s.set_style("font-weight", "bold")
s.set_style("text-align", "center")
expect(s.style.display).to_equal("flex")
expect(s.style.float_css).to_equal("left")
expect(s.style.clear_css).to_equal("both")
expect(s.style.overflow).to_equal("hidden")
expect(s.style.position).to_equal("absolute")
expect(s.style.color).to_equal("red")
expect(s.style.background_color).to_equal("blue")
expect(s.style.font_weight).to_equal("bold")
expect(s.style.text_align).to_equal("center")
```

</details>

#### ignores an unrecognised style property

- ignores an unrecognised style property
   - Expected: s.style.display equals `block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores an unrecognised style property")
var s = BeDomNode.element_with_id(2, "p")
s.set_style("display", "block")
s.set_style("unknown-prop", "x")
expect(s.style.display).to_equal("block")
```

</details>

### BeDomNode event listeners

#### clears a listener that is not the first registered

- clears a listener that is not the first registered
   - Expected: l.event_listener_types.len() equals `2`
   - Expected: l.event_listener_actions[0] equals `one`
   - Expected: l.event_listener_actions[1] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clears a listener that is not the first registered")
# Removal walks the list; tombstoning the second entry is what
# exercises the loop advance.
var l = BeDomNode.element_with_id(3, "button")
l.add_event_listener("click", "one")
l.add_event_listener("click", "two")
l.remove_event_listener("click", "two")
expect(l.event_listener_types.len()).to_equal(2)
expect(l.event_listener_actions[0]).to_equal("one")
expect(l.event_listener_actions[1]).to_equal("")
```

</details>

### BeDomEvent default handling

#### marks a cancelable event as default-prevented

- marks a cancelable event as default-prevented
   - Expected: e.default_prevented is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("marks a cancelable event as default-prevented")
var e = BeDomEvent.create("click", "", true, true)
e.prevent_default()
expect(e.default_prevented).to_equal(true)
```

</details>

#### leaves a non-cancelable event unchanged

- leaves a non-cancelable event unchanged
   - Expected: e.default_prevented is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves a non-cancelable event unchanged")
var e = BeDomEvent.create("click", "", true, false)
e.prevent_default()
expect(e.default_prevented).to_equal(false)
```

</details>

#### stops propagation

- stops propagation
   - Expected: e.propagation_stopped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stops propagation")
var e = BeDomEvent.create("click", "", true, false)
e.stop_propagation()
expect(e.propagation_stopped).to_equal(true)
```

</details>

### BeDomNode manual tree dump

#### walks a hand-built tree depth-first with attribute lengths intact

- walks a hand-built tree depth-first with attribute lengths intact
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `0|#root|style_len=0|childcount=1`
   - Expected: parts[1] equals `1|div|style_len=34|childcount=1`
   - Expected: parts[2] equals `2|#text|style_len=0|childcount=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("walks a hand-built tree depth-first with attribute lengths intact")
# The helper exists to bisect a JIT struct-field-read defect; it must
# report the style attribute's real length and the real child counts.
val parts = be_dom_debug_manual_tree_dump().split("\n")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("0|#root|style_len=0|childcount=1")
expect(parts[1]).to_equal("1|div|style_len=34|childcount=1")
expect(parts[2]).to_equal("2|#text|style_len=0|childcount=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_node_mutation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BeDomNode attributes, BeDomNode children, BeDomNode inline style, BeDomNode event listeners, BeDomEvent default handling, BeDomNode manual tree dump.
- BeDomNode attributes
- BeDomNode children
- BeDomNode inline style
- BeDomNode event listeners
- BeDomEvent default handling
- BeDomNode manual tree dump

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `8ae7ef5b6d933224d736ee14583cf3f24b488fed17bfea750451a9cfe45a3761`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ae7ef5b6d933224d736ee14583cf3f24b488fed17bfea750451a9cfe45a3761`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ae7ef5b6d933224d736ee14583cf3f24b488fed17bfea750451a9cfe45a3761`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_node_mutation_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_node_mutation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_node_mutation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_node_mutation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_node_mutation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_node_mutation_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores an attribute and reads it back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_node_mutation_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores the three render-cache-invalidating attributes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_node_mutation_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes a render-cache-invalidating attribute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
