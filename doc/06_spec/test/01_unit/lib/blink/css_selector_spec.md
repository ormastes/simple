# CSS Selector Matcher Specification

> Tests for `parse_selector` (tokenisation + AST construction) and `matches_compound` (single-element matching logic) defined in `src/lib/blink/css_parser/selector.spl`.

<!-- sdn-diagram:id=css_selector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=css_selector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

css_selector_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=css_selector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `parse_selector` (tokenisation + AST construction) and
`matches_compound` (single-element matching logic) defined in
`src/lib/blink/css_parser/selector.spl`.

## Scenarios

### parse_selector: type selector

#### div produces 1 compound with Type selector

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_selector("div")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(1)
val simple = compound.simples[0]
expect(simple.kind == SimpleSelectorKind.Type).to_equal(true)
expect(simple.name).to_equal("div")
```

</details>

### parse_selector: class selector

#### .foo produces 1 compound with Class selector

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_selector(".foo")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(1)
val simple = compound.simples[0]
expect(simple.kind == SimpleSelectorKind.Class).to_equal(true)
expect(simple.name).to_equal("foo")
```

</details>

### parse_selector: id selector

#### #bar produces 1 compound with Id selector

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_selector("#bar")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(1)
val simple = compound.simples[0]
expect(simple.kind == SimpleSelectorKind.Id).to_equal(true)
expect(simple.name).to_equal("bar")
```

</details>

### parse_selector: compound selector

#### div.foo produces 1 compound with 2 simples (Type + Class)

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_selector("div.foo")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(2)
val s0 = compound.simples[0]
val s1 = compound.simples[1]
expect(s0.kind == SimpleSelectorKind.Type).to_equal(true)
expect(s0.name).to_equal("div")
expect(s1.kind == SimpleSelectorKind.Class).to_equal(true)
expect(s1.name).to_equal("foo")
```

</details>

### parse_selector: descendant combinator

#### div p produces 2 compounds with Descendant combinator

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_selector("div p")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(2)
expect(sel.combinators.len()).to_equal(1)
expect(sel.combinators[0] == Combinator.Descendant).to_equal(true)
expect(sel.compounds[0].simples[0].name).to_equal("div")
expect(sel.compounds[1].simples[0].name).to_equal("p")
```

</details>

### parse_selector: child combinator

#### ul > li produces 2 compounds with Child combinator

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_selector("ul > li")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(2)
expect(sel.combinators.len()).to_equal(1)
expect(sel.combinators[0] == Combinator.Child).to_equal(true)
expect(sel.compounds[0].simples[0].name).to_equal("ul")
expect(sel.compounds[1].simples[0].name).to_equal("li")
```

</details>

### matches_compound: type selector

#### node with tag div matches type selector div

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_selector(".btn:hover")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(2)
val s0 = compound.simples[0]
val s1 = compound.simples[1]
expect(s0.kind == SimpleSelectorKind.Class).to_equal(true)
expect(s0.name).to_equal("btn")
expect(s1.kind == SimpleSelectorKind.PseudoClass).to_equal(true)
expect(s1.name).to_equal("hover")
```

</details>

### parse_selector: pseudo-class :focus

#### #input:focus produces 1 compound with 2 simples (Id + PseudoClass)

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_selector("#input:focus")
expect(result.is_none()).to_equal(false)
val sel = result.unwrap()
expect(sel.compounds.len()).to_equal(1)
val compound = sel.compounds[0]
expect(compound.simples.len()).to_equal(2)
val s0 = compound.simples[0]
val s1 = compound.simples[1]
expect(s0.kind == SimpleSelectorKind.Id).to_equal(true)
expect(s0.name).to_equal("input")
expect(s1.kind == SimpleSelectorKind.PseudoClass).to_equal(true)
expect(s1.name).to_equal("focus")
```

</details>

### parse_selector: rejects unsupported pseudo-class

#### :nth-child(2) returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_selector(":nth-child(2)")
expect(result.is_none()).to_equal(true)
```

</details>

### matches_compound_with_state: :hover

#### .btn:hover matches when hovered_id equals node id

1. node attributes push
   - Expected: result.is_none() is false
   - Expected: matches_compound_with_state(node, 7, compound, state) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. node attributes push
   - Expected: result.is_none() is false
   - Expected: matches_compound_with_state(node, 7, compound, state) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. node attributes push
   - Expected: result.is_none() is false
   - Expected: matches_compound_with_state(node, 11, compound, state) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. node attributes push
   - Expected: result.is_none() is false
   - Expected: matches_compound_with_state(node, 11, compound, state) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
