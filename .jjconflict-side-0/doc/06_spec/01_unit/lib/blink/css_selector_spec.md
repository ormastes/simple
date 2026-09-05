# CSS Selector Matcher Specification

> Tests for `parse_selector` (tokenisation + AST construction) and `matches_compound` (single-element matching logic) defined in `src/lib/blink/css_parser/selector.spl`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Selector Matcher Specification

Tests for `parse_selector` (tokenisation + AST construction) and `matches_compound` (single-element matching logic) defined in `src/lib/blink/css_parser/selector.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/01_unit/lib/blink/css_selector_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `parse_selector` (tokenisation + AST construction) and
`matches_compound` (single-element matching logic) defined in
`src/lib/blink/css_parser/selector.spl`.

## Scenarios

### parse_selector: type selector

#### div produces 1 compound with Type selector

- div produces 1 compound with Type selector
   - Expected: result.is_none() is false
   - Expected: sel.compounds.len() equals `1`
   - Expected: compound.simples.len() equals `1`
   - Expected: simple.kind equals `SimpleSelectorKind.Type`
   - Expected: simple.name equals `div`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("div produces 1 compound with Type selector")
val result = parse_selector("div")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(1)
val simple = compound.simples[0]
expect(simple.kind).to_equal(SimpleSelectorKind.Type)
expect(simple.name).to_equal("div")
```

</details>

### parse_selector: class selector

#### .foo produces 1 compound with Class selector

- .foo produces 1 compound with Class selector
   - Expected: result.is_none() is false
   - Expected: sel.compounds.len() equals `1`
   - Expected: compound.simples.len() equals `1`
   - Expected: simple.kind equals `SimpleSelectorKind.Class`
   - Expected: simple.name equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step(".foo produces 1 compound with Class selector")
val result = parse_selector(".foo")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(1)
val simple = compound.simples[0]
expect(simple.kind).to_equal(SimpleSelectorKind.Class)
expect(simple.name).to_equal("foo")
```

</details>

### parse_selector: id selector

#### #bar produces 1 compound with Id selector

- #bar produces 1 compound with Id selector
   - Expected: result.is_none() is false
   - Expected: sel.compounds.len() equals `1`
   - Expected: compound.simples.len() equals `1`
   - Expected: simple.kind equals `SimpleSelectorKind.Id`
   - Expected: simple.name equals `bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("#bar produces 1 compound with Id selector")
val result = parse_selector("#bar")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(1)
val simple = compound.simples[0]
expect(simple.kind).to_equal(SimpleSelectorKind.Id)
expect(simple.name).to_equal("bar")
```

</details>

### parse_selector: compound selector

#### div.foo produces 1 compound with 2 simples (Type + Class)

- div.foo produces 1 compound with 2 simples (Type + Class)
   - Expected: result.is_none() is false
   - Expected: sel.compounds.len() equals `1`
   - Expected: compound.simples.len() equals `2`
   - Expected: s0.kind equals `SimpleSelectorKind.Type`
   - Expected: s0.name equals `div`
   - Expected: s1.kind equals `SimpleSelectorKind.Class`
   - Expected: s1.name equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("div.foo produces 1 compound with 2 simples (Type + Class)")
val result = parse_selector("div.foo")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(2)
val s0 = compound.simples[0]
val s1 = compound.simples[1]
expect(s0.kind).to_equal(SimpleSelectorKind.Type)
expect(s0.name).to_equal("div")
expect(s1.kind).to_equal(SimpleSelectorKind.Class)
expect(s1.name).to_equal("foo")
```

</details>

### parse_selector: descendant combinator

#### div p produces 2 compounds with Descendant combinator

- div p produces 2 compounds with Descendant combinator
   - Expected: result.is_none() is false
   - Expected: sel.compounds.len() equals `2`
   - Expected: sel.combinators.len() equals `1`
   - Expected: sel.combinators[0] equals `Combinator.Descendant`
   - Expected: sel.compounds[0].simples[0].name equals `div`
   - Expected: sel.compounds[1].simples[0].name equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("div p produces 2 compounds with Descendant combinator")
val result = parse_selector("div p")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(2)
expect(sel.combinators.len()).to_equal(1)
expect(sel.combinators[0]).to_equal(Combinator.Descendant)
expect(sel.compounds[0].simples[0].name).to_equal("div")
expect(sel.compounds[1].simples[0].name).to_equal("p")
```

</details>

### parse_selector: child combinator

#### ul > li produces 2 compounds with Child combinator

- ul > li produces 2 compounds with Child combinator
   - Expected: result.is_none() is false
   - Expected: sel.compounds.len() equals `2`
   - Expected: sel.combinators.len() equals `1`
   - Expected: sel.combinators[0] equals `Combinator.Child`
   - Expected: sel.compounds[0].simples[0].name equals `ul`
   - Expected: sel.compounds[1].simples[0].name equals `li`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ul > li produces 2 compounds with Child combinator")
val result = parse_selector("ul > li")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(2)
expect(sel.combinators.len()).to_equal(1)
expect(sel.combinators[0]).to_equal(Combinator.Child)
expect(sel.compounds[0].simples[0].name).to_equal("ul")
expect(sel.compounds[1].simples[0].name).to_equal("li")
```

</details>

### matches_compound: type selector

#### node with tag div matches type selector div

- node with tag div matches type selector div
   - Expected: result.is_none() is false
   - Expected: matches_compound(node, compound) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("node with tag div matches type selector div")
val node = dom_node_new(1, NodeType.Element)
node.tag_name = "div"
val result = parse_selector("div")
expect(result.is_none()).to_equal(false)
val compound = result.unwrap().compounds[0]
expect(matches_compound(node, compound)).to_equal(true)
```

</details>

### matches_compound: class selector

#### node without class foo does not match .foo selector

- node without class foo does not match .foo selector
   - Expected: result.is_none() is false
   - Expected: matches_compound(node, compound) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("node without class foo does not match .foo selector")
val node = dom_node_new(2, NodeType.Element)
node.tag_name = "div"
# No class attribute — should not match.
val result = parse_selector(".foo")
expect(result.is_none()).to_equal(false)
val compound = result.unwrap().compounds[0]
expect(matches_compound(node, compound)).to_equal(false)
```

</details>

### parse_selector: pseudo-class :hover

#### .btn:hover produces 1 compound with 2 simples (Class + PseudoClass)

- .btn:hover produces 1 compound with 2 simples (Class + PseudoClass)
   - Expected: result.is_none() is false
   - Expected: sel.compounds.len() equals `1`
   - Expected: compound.simples.len() equals `2`
   - Expected: s0.kind equals `SimpleSelectorKind.Class`
   - Expected: s0.name equals `btn`
   - Expected: s1.kind equals `SimpleSelectorKind.PseudoClass`
   - Expected: s1.name equals `hover`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step(".btn:hover produces 1 compound with 2 simples (Class + PseudoClass)")
val result = parse_selector(".btn:hover")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(2)
val s0 = compound.simples[0]
val s1 = compound.simples[1]
expect(s0.kind).to_equal(SimpleSelectorKind.Class)
expect(s0.name).to_equal("btn")
expect(s1.kind).to_equal(SimpleSelectorKind.PseudoClass)
expect(s1.name).to_equal("hover")
```

</details>

### parse_selector: pseudo-class :focus

#### #input:focus produces 1 compound with 2 simples (Id + PseudoClass)

- #input:focus produces 1 compound with 2 simples (Id + PseudoClass)
   - Expected: result.is_none() is false
   - Expected: sel.compounds.len() equals `1`
   - Expected: compound.simples.len() equals `2`
   - Expected: s0.kind equals `SimpleSelectorKind.Id`
   - Expected: s0.name equals `input`
   - Expected: s1.kind equals `SimpleSelectorKind.PseudoClass`
   - Expected: s1.name equals `focus`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("#input:focus produces 1 compound with 2 simples (Id + PseudoClass)")
val result = parse_selector("#input:focus")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(2)
val s0 = compound.simples[0]
val s1 = compound.simples[1]
expect(s0.kind).to_equal(SimpleSelectorKind.Id)
expect(s0.name).to_equal("input")
expect(s1.kind).to_equal(SimpleSelectorKind.PseudoClass)
expect(s1.name).to_equal("focus")
```

</details>

### parse_selector: rejects unsupported pseudo-class

#### :nth-child(2) returns None

- :nth-child(2) returns None
   - Expected: result.is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step(":nth-child(2) returns None")
val result = parse_selector(":nth-child(2)")
expect(result.is_none()).to_equal(true)
```

</details>

### matches_compound_with_state: :hover

#### .btn:hover matches when hovered_id equals node id

- .btn:hover matches when hovered_id equals node id
   - Expected: result.is_none() is false
   - Expected: matches_compound_with_state(node, 7, compound, state) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step(".btn:hover matches when hovered_id equals node id")
val node = dom_node_new(7, NodeType.Element)
node.tag_name = "button"
node.attributes.push(attribute_new("class", "btn"))
val result = parse_selector(".btn:hover")
expect(result.is_none()).to_equal(false)
val compound = result.unwrap().compounds[0]
val state = interaction_state_with_hover(7)
expect(matches_compound_with_state(node, 7, compound, state)).to_equal(true)
```

</details>

#### .btn:hover does NOT match when hovered_id is -1

- .btn:hover does NOT match when hovered_id is -1
   - Expected: result.is_none() is false
   - Expected: matches_compound_with_state(node, 7, compound, state) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step(".btn:hover does NOT match when hovered_id is -1")
val node = dom_node_new(7, NodeType.Element)
node.tag_name = "button"
node.attributes.push(attribute_new("class", "btn"))
val result = parse_selector(".btn:hover")
expect(result.is_none()).to_equal(false)
val compound = result.unwrap().compounds[0]
val state = interaction_state_empty()
expect(matches_compound_with_state(node, 7, compound, state)).to_equal(false)
```

</details>

### matches_compound_with_state: :focus

#### #input:focus matches when focused_id equals node id

- #input:focus matches when focused_id equals node id
   - Expected: result.is_none() is false
   - Expected: matches_compound_with_state(node, 11, compound, state) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("#input:focus matches when focused_id equals node id")
val node = dom_node_new(11, NodeType.Element)
node.tag_name = "input"
node.attributes.push(attribute_new("id", "input"))
val result = parse_selector("#input:focus")
expect(result.is_none()).to_equal(false)
val compound = result.unwrap().compounds[0]
val state = interaction_state_with_focus(11)
expect(matches_compound_with_state(node, 11, compound, state)).to_equal(true)
```

</details>

#### #input:focus does NOT match when focused_id is -1

- #input:focus does NOT match when focused_id is -1
   - Expected: result.is_none() is false
   - Expected: matches_compound_with_state(node, 11, compound, state) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("#input:focus does NOT match when focused_id is -1")
val node = dom_node_new(11, NodeType.Element)
node.tag_name = "input"
node.attributes.push(attribute_new("id", "input"))
val result = parse_selector("#input:focus")
expect(result.is_none()).to_equal(false)
val compound = result.unwrap().compounds[0]
val state = interaction_state_empty()
expect(matches_compound_with_state(node, 11, compound, state)).to_equal(false)
```

</details>

### matches_complex: descendant combinator over the tree

#### div p matches a p nested two levels below the div

- div p matches a p nested two levels below the div
- build document > div > section > p
- match the p against selector 'div p'
   - Expected: matches_complex(tree, p_id, sel) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("div p matches a p nested two levels below the div")
step("build document > div > section > p")
var tree = dom_tree_new()
val div_id = tree.create_element("div")
val section_id = tree.create_element("section")
val p_id = tree.create_element("p")
tree.append_child(0, div_id)
tree.append_child(div_id, section_id)
tree.append_child(section_id, p_id)
step("match the p against selector 'div p'")
val sel = parse_selector("div p").unwrap()
expect(matches_complex(tree, p_id, sel)).to_equal(true)
```

</details>

#### div p does NOT match a p that is outside the div

- div p does NOT match a p that is outside the div
- build document > div (empty) and document > p as siblings
- match the sibling p against 'div p' and expect a rejection
   - Expected: matches_complex(tree, p_id, sel) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("div p does NOT match a p that is outside the div")
step("build document > div (empty) and document > p as siblings")
var tree = dom_tree_new()
val div_id = tree.create_element("div")
val p_id = tree.create_element("p")
tree.append_child(0, div_id)
tree.append_child(0, p_id)
step("match the sibling p against 'div p' and expect a rejection")
val sel = parse_selector("div p").unwrap()
expect(matches_complex(tree, p_id, sel)).to_equal(false)
```

</details>

### matches_complex: child combinator requires the IMMEDIATE parent

#### ul > li matches an li whose direct parent is the ul

- ul > li matches an li whose direct parent is the ul
- build document > ul > li
- match the li against 'ul > li'
   - Expected: matches_complex(tree, li_id, sel) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ul > li matches an li whose direct parent is the ul")
step("build document > ul > li")
var tree = dom_tree_new()
val ul_id = tree.create_element("ul")
val li_id = tree.create_element("li")
tree.append_child(0, ul_id)
tree.append_child(ul_id, li_id)
step("match the li against 'ul > li'")
val sel = parse_selector("ul > li").unwrap()
expect(matches_complex(tree, li_id, sel)).to_equal(true)
```

</details>

#### div > p rejects a p whose parent is a section INSIDE the div

- div > p rejects a p whose parent is a section INSIDE the div
- build document > div > section > p — p is a grandchild of div
- child combinator must reject the grandchild; descendant must accept it
   - Expected: matches_complex(tree, p_id, child_sel) is false
   - Expected: matches_complex(tree, p_id, desc_sel) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("div > p rejects a p whose parent is a section INSIDE the div")
step("build document > div > section > p — p is a grandchild of div")
var tree = dom_tree_new()
val div_id = tree.create_element("div")
val section_id = tree.create_element("section")
val p_id = tree.create_element("p")
tree.append_child(0, div_id)
tree.append_child(div_id, section_id)
tree.append_child(section_id, p_id)
step("child combinator must reject the grandchild; descendant must accept it")
val child_sel = parse_selector("div > p").unwrap()
expect(matches_complex(tree, p_id, child_sel)).to_equal(false)
val desc_sel = parse_selector("div p").unwrap()
expect(matches_complex(tree, p_id, desc_sel)).to_equal(true)
```

</details>

### matches_complex: right-to-left anchoring on the candidate node

#### div p anchors on the rightmost compound: the div itself never matches

- div p anchors on the rightmost compound: the div itself never matches
- build document > div > p
- candidate is the DIV — rightmost compound 'p' must fail on it
   - Expected: matches_complex(tree, div_id, sel) is false
- candidate is the P — the same selector matches
   - Expected: matches_complex(tree, p_id, sel) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("div p anchors on the rightmost compound: the div itself never matches")
step("build document > div > p")
var tree = dom_tree_new()
val div_id = tree.create_element("div")
val p_id = tree.create_element("p")
tree.append_child(0, div_id)
tree.append_child(div_id, p_id)
step("candidate is the DIV — rightmost compound 'p' must fail on it")
val sel = parse_selector("div p").unwrap()
expect(matches_complex(tree, div_id, sel)).to_equal(false)
step("candidate is the P — the same selector matches")
expect(matches_complex(tree, p_id, sel)).to_equal(true)
```

</details>

### matches_complex: three-compound chain mixing both combinators

#### div ul > li matches only when the li's parent is a ul under a div

- div ul > li matches only when the li's parent is a ul under a div
- build document > div > ul > li  AND  document > ol > li
- the ul-parented li matches; the ol-parented li does not
   - Expected: matches_complex(tree, li_id, sel) is true
   - Expected: matches_complex(tree, stray_li, sel) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("div ul > li matches only when the li's parent is a ul under a div")
step("build document > div > ul > li  AND  document > ol > li")
var tree = dom_tree_new()
val div_id = tree.create_element("div")
val ul_id = tree.create_element("ul")
val li_id = tree.create_element("li")
val ol_id = tree.create_element("ol")
val stray_li = tree.create_element("li")
tree.append_child(0, div_id)
tree.append_child(div_id, ul_id)
tree.append_child(ul_id, li_id)
tree.append_child(0, ol_id)
tree.append_child(ol_id, stray_li)
step("the ul-parented li matches; the ol-parented li does not")
val sel = parse_selector("div ul > li").unwrap()
expect(matches_complex(tree, li_id, sel)).to_equal(true)
expect(matches_complex(tree, stray_li, sel)).to_equal(false)
```

</details>

### matches_complex: descendant walk must consider EVERY matching ancestor

#### .a > .b .c matches when a farther .b ancestor satisfies the child step

- .a > .b .c matches when a farther .b ancestor satisfies the child step
- build document > x(.a) > y(.b) > z(.b) > c(.c)
- the NEAREST .b ancestor (z) fails '.a > .b', but y succeeds — a greedy walk without backtracking wrongly rejects
   - Expected: matches_complex(tree, c_id, sel) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step(".a > .b .c matches when a farther .b ancestor satisfies the child step")
step("build document > x(.a) > y(.b) > z(.b) > c(.c)")
var tree = dom_tree_new()
val x_id = tree.create_element("div")
tree.set_attribute(x_id, "class", "a")
val y_id = tree.create_element("div")
tree.set_attribute(y_id, "class", "b")
val z_id = tree.create_element("div")
tree.set_attribute(z_id, "class", "b")
val c_id = tree.create_element("span")
tree.set_attribute(c_id, "class", "c")
tree.append_child(0, x_id)
tree.append_child(x_id, y_id)
tree.append_child(y_id, z_id)
tree.append_child(z_id, c_id)
step("the NEAREST .b ancestor (z) fails '.a > .b', but y succeeds — a greedy walk without backtracking wrongly rejects")
val sel = parse_selector(".a > .b .c").unwrap()
expect(matches_complex(tree, c_id, sel)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `e5cc3dab1da76fd72fbe115104e0991eb55a963298d27cf2f930bf9a66efcdb3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5cc3dab1da76fd72fbe115104e0991eb55a963298d27cf2f930bf9a66efcdb3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5cc3dab1da76fd72fbe115104e0991eb55a963298d27cf2f930bf9a66efcdb3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/blink/css_selector_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/css_selector_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/blink/css_selector_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/css_selector_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/css_selector_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/blink/css_selector_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'div produces 1 compound with Type selector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/css_selector_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '.foo produces 1 compound with Class selector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/css_selector_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '#bar produces 1 compound with Id selector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
