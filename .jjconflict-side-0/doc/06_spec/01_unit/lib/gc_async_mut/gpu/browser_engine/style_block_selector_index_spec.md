# Style Block Selector Index Specification

> Tests covering selector_bucket_discriminant, selector_index_candidates, selector index equivalence vs linear scan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style Block Selector Index Specification

## Scenarios

### selector_bucket_discriminant

#### buckets a plain id selector under id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- buckets a plain id selector under id
   - Expected: kk[0] equals `id`
   - Expected: kk[1] equals `target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("buckets a plain id selector under id")
val kk = selector_bucket_discriminant("#target")
expect(kk[0]).to_equal("id")
expect(kk[1]).to_equal("target")
```

</details>

#### buckets a plain class selector under class

- buckets a plain class selector under class
   - Expected: kk[0] equals `class`
   - Expected: kk[1] equals `alpha`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("buckets a plain class selector under class")
val kk = selector_bucket_discriminant(".alpha")
expect(kk[0]).to_equal("class")
expect(kk[1]).to_equal("alpha")
```

</details>

#### buckets a compound tag.class under class (necessary-condition bucket)

- buckets a compound tag.class under class (necessary-condition bucket)
   - Expected: kk[0] equals `class`
   - Expected: kk[1] equals `container`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("buckets a compound tag.class under class (necessary-condition bucket)")
val kk = selector_bucket_discriminant("div.container")
expect(kk[0]).to_equal("class")
expect(kk[1]).to_equal("container")
```

</details>

#### buckets a plain tag selector under tag

- buckets a plain tag selector under tag
   - Expected: kk[0] equals `tag`
   - Expected: kk[1] equals `span`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("buckets a plain tag selector under tag")
val kk = selector_bucket_discriminant("span")
expect(kk[0]).to_equal("tag")
expect(kk[1]).to_equal("span")
```

</details>

#### buckets universal selector under universal

- buckets universal selector under universal
   - Expected: kk[0] equals `universal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("buckets universal selector under universal")
val kk = selector_bucket_discriminant("*")
expect(kk[0]).to_equal("universal")
```

</details>

#### buckets attribute selectors under universal (not cheaply discriminable)

- buckets attribute selectors under universal (not cheaply discriminable)
   - Expected: kk[0] equals `universal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("buckets attribute selectors under universal (not cheaply discriminable)")
val kk = selector_bucket_discriminant("div[data-x]")
expect(kk[0]).to_equal("universal")
```

</details>

#### buckets a descendant combinator by its LAST simple selector

- buckets a descendant combinator by its LAST simple selector
   - Expected: kk[0] equals `class`
   - Expected: kk[1] equals `alpha`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("buckets a descendant combinator by its LAST simple selector")
val kk = selector_bucket_discriminant("section .alpha")
expect(kk[0]).to_equal("class")
expect(kk[1]).to_equal("alpha")
```

</details>

#### buckets a child combinator by its LAST simple selector

- buckets a child combinator by its LAST simple selector
   - Expected: kk[0] equals `id`
   - Expected: kk[1] equals `target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("buckets a child combinator by its LAST simple selector")
val kk = selector_bucket_discriminant("div > #target")
expect(kk[0]).to_equal("id")
expect(kk[1]).to_equal("target")
```

</details>

### selector_index_candidates

#### returns empty-tag/empty-id/no-class candidates as only the universal bucket

- returns empty-tag/empty-id/no-class candidates as only the universal bucket
   - Expected: cands.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty-tag/empty-id/no-class candidates as only the universal bucket")
val rules = [rule("*", "color", "red")]
val idx = build_selector_rule_index(rules)
val cands = selector_index_candidates(idx, "div", "", [])
expect(cands.len()).to_equal(1)
```

</details>

### selector index equivalence vs linear scan

#### produces identical results for no matches

- produces identical results for no matches
   - Expected: colors_flat(tree_a) equals `colors_flat(tree_b)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces identical results for no matches")
val rules = [rule(".nowhere", "background-color", "red")]
val tree_a = build_tree()
val tree_b = build_tree()
apply_css_rules_to_tree_linear(tree_a, rules)
apply_css_rules_to_tree(tree_b, rules)
expect(colors_flat(tree_a)).to_equal(colors_flat(tree_b))
```

</details>

#### produces identical results across multiple candidate buckets (tag+class+id+universal)

- produces identical results across multiple candidate buckets (tag+class+id+universal)
   - Expected: colors_flat(tree_a) equals `colors_flat(tree_b)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces identical results across multiple candidate buckets (tag+class+id+universal)")
val rules = [
    rule("*", "background-color", "gray"),
    rule("div", "background-color", "blue"),
    rule(".beta", "background-color", "green"),
    rule("#target", "background-color", "yellow"),
    rule("div.container", "background-color", "purple"),
    rule("section .alpha", "background-color", "orange")]
val tree_a = build_tree()
val tree_b = build_tree()
apply_css_rules_to_tree_linear(tree_a, rules)
apply_css_rules_to_tree(tree_b, rules)
expect(colors_flat(tree_a)).to_equal(colors_flat(tree_b))
```

</details>

#### produces identical results with an empty ruleset

- produces identical results with an empty ruleset
   - Expected: colors_flat(tree_a) equals `colors_flat(tree_b)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces identical results with an empty ruleset")
val rules: [CssRule] = []
val tree_a = build_tree()
val tree_b = build_tree()
apply_css_rules_to_tree_linear(tree_a, rules)
apply_css_rules_to_tree(tree_b, rules)
expect(colors_flat(tree_a)).to_equal(colors_flat(tree_b))
```

</details>

#### produces identical results for a node with no class or id

- produces identical results for a node with no class or id
   - Expected: colors_flat(tree_a) equals `colors_flat(tree_b)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces identical results for a node with no class or id")
val rules = [
    rule("em", "background-color", "pink"),
    rule("*", "background-color", "gray")]
val tree_a = build_tree()
val tree_b = build_tree()
apply_css_rules_to_tree_linear(tree_a, rules)
apply_css_rules_to_tree(tree_b, rules)
expect(colors_flat(tree_a)).to_equal(colors_flat(tree_b))
```

</details>

#### matches the universal selector identically on both paths

- matches the universal selector identically on both paths
   - Expected: colors_flat(tree_b) equals `colors_flat(tree_a)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the universal selector identically on both paths")
val rules = [rule("*", "background-color", "teal")]
val tree_a = build_tree()
val tree_b = build_tree()
apply_css_rules_to_tree_linear(tree_a, rules)
apply_css_rules_to_tree(tree_b, rules)
expect(colors_flat(tree_b)).to_equal(colors_flat(tree_a))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_selector_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering selector_bucket_discriminant, selector_index_candidates, selector index equivalence vs linear scan.
- selector_bucket_discriminant
- selector_index_candidates
- selector index equivalence vs linear scan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `a343f5003eab61a1f506f9a7788c00d94cfd45a385bbe395b89088dbe50fc147`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a343f5003eab61a1f506f9a7788c00d94cfd45a385bbe395b89088dbe50fc147`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a343f5003eab61a1f506f9a7788c00d94cfd45a385bbe395b89088dbe50fc147`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_selector_index_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_selector_index_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_selector_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_selector_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_selector_index_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_selector_index_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'buckets a plain id selector under id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_selector_index_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'buckets a plain class selector under class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_selector_index_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'buckets a compound tag.class under class (necessary-condition bucket)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
