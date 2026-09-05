# HTML Layout Renderer Core — Pure-Helper Coverage Closure (U4.4, part N)

> `simple_web_html_layout_renderer_core.spl` measured 53% (1114/2075 lines) via

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 69 | 69 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Layout Renderer Core — Pure-Helper Coverage Closure (U4.4, part N)

`simple_web_html_layout_renderer_core.spl` measured 53% (1114/2075 lines) via

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`simple_web_html_layout_renderer_core.spl` measured 53% (1114/2075 lines) via
a throwaway single-@cover copy of `simple_web_html_layout_renderer_coverage_spec.spl`
(the only spec exercising this file), banner AND artifact confirmed
(`/tmp/u44core/base.sdn`). This closure spec targets the largest
zero/low-coverage PURE module-level helpers (no DOM-tree fixture needed) that
were reachable only indirectly through full-document rendering before:
`_css_root_prefix_is_preamble`, `_is_interaction_state_pseudo`,
`_nth_child_matches`, `_part_specificity`, `_group_specificity`,
`_sort_candidates_by_specificity`, `_sort_positive_z_indices`,
`_sort_style_order_indices`, `merge_two_sorted_rule_lists_unique`,
`merge_sorted_rule_lists_unique_count`, `rule_lists_from_counts`,
`selector_bucket_value_from_base`, `text_seen_before`, `i32_list_prefix`,
`text_key_index_count`, `dict_key_index_count`, `attr_selector_matches`,
`base_selector_matches`, `class_words_has`, `class_has_all`, `unquote_css_attr_value`.

These are module-level `fn` (not `pub fn`) but directly importable in-project
(confirmed by the existing `simple_web_html_layout_renderer_style_coverage_closure_spec.spl`
precedent, which imports non-`pub` helpers from a sibling file the same way).

Every assertion below is a real oracle: expected values independently
traced by hand against the source algorithm shown in
`simple_web_html_layout_renderer_core.spl` (specificity is the standard CSS
scoring: id=100, class/attr/pseudo-class=10, type=1; merge functions are
verified by manual trace of the sorted-unique merge).

No smoke tests (bare calls with no assertion).

## Scenarios

### core.spl: _css_root_prefix_is_preamble

#### accepts an empty/whitespace-only prefix

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts an empty/whitespace-only prefix
   - Expected: _css_root_prefix_is_preamble("") is true
   - Expected: _css_root_prefix_is_preamble("   ") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts an empty/whitespace-only prefix")
expect(_css_root_prefix_is_preamble("")).to_equal(true)
expect(_css_root_prefix_is_preamble("   ")).to_equal(true)
```

</details>

#### accepts a comment-only preamble

- accepts a comment-only preamble
   - Expected: _css_root_prefix_is_preamble("/* c */") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a comment-only preamble")
expect(_css_root_prefix_is_preamble("/* c */")).to_equal(true)
```

</details>

#### accepts an at-rule preamble terminated by ;

- accepts an at-rule preamble terminated by ;
   - Expected: _css_root_prefix_is_preamble("@media screen;") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts an at-rule preamble terminated by ;")
expect(_css_root_prefix_is_preamble("@media screen;")).to_equal(true)
```

</details>

#### rejects an at-rule preamble whose { comes before ;

- rejects an at-rule preamble whose { comes before ;
   - Expected: _css_root_prefix_is_preamble("@media screen{") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an at-rule preamble whose { comes before ;")
expect(_css_root_prefix_is_preamble("@media screen{")).to_equal(false)
```

</details>

#### rejects a non-comment non-at-rule prefix

- rejects a non-comment non-at-rule prefix
   - Expected: _css_root_prefix_is_preamble("body ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-comment non-at-rule prefix")
expect(_css_root_prefix_is_preamble("body ")).to_equal(false)
```

</details>

#### rejects an unterminated comment

- rejects an unterminated comment
   - Expected: _css_root_prefix_is_preamble("/* unterminated") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an unterminated comment")
expect(_css_root_prefix_is_preamble("/* unterminated")).to_equal(false)
```

</details>

### core.spl: _is_interaction_state_pseudo

#### recognizes every unconditional interaction pseudo-class

- recognizes every unconditional interaction pseudo-class
   - Expected: _is_interaction_state_pseudo("hover", "") is true
   - Expected: _is_interaction_state_pseudo("active", "") is true
   - Expected: _is_interaction_state_pseudo("focus", "") is true
   - Expected: _is_interaction_state_pseudo("focus-visible", "") is true
   - Expected: _is_interaction_state_pseudo("focus-within", "") is true
   - Expected: _is_interaction_state_pseudo("visited", "") is true
   - Expected: _is_interaction_state_pseudo("target", "") is true
   - Expected: _is_interaction_state_pseudo("checked", "") is true
   - Expected: _is_interaction_state_pseudo("placeholder-shown", "") is true
   - Expected: _is_interaction_state_pseudo("autofill", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("recognizes every unconditional interaction pseudo-class")
expect(_is_interaction_state_pseudo("hover", "")).to_equal(true)
expect(_is_interaction_state_pseudo("active", "")).to_equal(true)
expect(_is_interaction_state_pseudo("focus", "")).to_equal(true)
expect(_is_interaction_state_pseudo("focus-visible", "")).to_equal(true)
expect(_is_interaction_state_pseudo("focus-within", "")).to_equal(true)
expect(_is_interaction_state_pseudo("visited", "")).to_equal(true)
expect(_is_interaction_state_pseudo("target", "")).to_equal(true)
expect(_is_interaction_state_pseudo("checked", "")).to_equal(true)
expect(_is_interaction_state_pseudo("placeholder-shown", "")).to_equal(true)
expect(_is_interaction_state_pseudo("autofill", "")).to_equal(true)
```

</details>

#### treats :disabled as interaction-state only when the disabled attr is absent

- treats :disabled as interaction-state only when the disabled attr is absent
   - Expected: _is_interaction_state_pseudo("disabled", "") is true
   - Expected: _is_interaction_state_pseudo("disabled", "disabled") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats :disabled as interaction-state only when the disabled attr is absent")
expect(_is_interaction_state_pseudo("disabled", "")).to_equal(true)
expect(_is_interaction_state_pseudo("disabled", "disabled")).to_equal(false)
```

</details>

#### rejects an unknown pseudo-class name

- rejects an unknown pseudo-class name
   - Expected: _is_interaction_state_pseudo("nth-child", "") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an unknown pseudo-class name")
expect(_is_interaction_state_pseudo("nth-child", "")).to_equal(false)
```

</details>

### core.spl: _nth_child_matches

#### matches the odd/even keywords

- matches the odd/even keywords
   - Expected: _nth_child_matches("odd", 1) is true
   - Expected: _nth_child_matches("odd", 2) is false
   - Expected: _nth_child_matches("even", 2) is true
   - Expected: _nth_child_matches("even", 3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the odd/even keywords")
expect(_nth_child_matches("odd", 1)).to_equal(true)
expect(_nth_child_matches("odd", 2)).to_equal(false)
expect(_nth_child_matches("even", 2)).to_equal(true)
expect(_nth_child_matches("even", 3)).to_equal(false)
```

</details>

#### matches an+b with positive a

- matches an+b with positive a
   - Expected: _nth_child_matches("2n+1", 1) is true
   - Expected: _nth_child_matches("2n+1", 2) is false
   - Expected: _nth_child_matches("2n+1", 5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches an+b with positive a")
# 2n+1 -> 1, 3, 5, ...
expect(_nth_child_matches("2n+1", 1)).to_equal(true)
expect(_nth_child_matches("2n+1", 2)).to_equal(false)
expect(_nth_child_matches("2n+1", 5)).to_equal(true)
```

</details>

#### matches n+b with implicit a=1

- matches n+b with implicit a=1
   - Expected: _nth_child_matches("n+3", 3) is true
   - Expected: _nth_child_matches("n+3", 2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches n+b with implicit a=1")
expect(_nth_child_matches("n+3", 3)).to_equal(true)
expect(_nth_child_matches("n+3", 2)).to_equal(false)
```

</details>

#### matches -n+b with implicit a=-1

- matches -n+b with implicit a=-1
   - Expected: _nth_child_matches("-n+3", 3) is true
   - Expected: _nth_child_matches("-n+3", 2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches -n+b with implicit a=-1")
# -n+3: rem = pos - 3; rem < 0 -> false (pos=2); rem >= 0 -> true
# (any rem is divisible by -1, so pos=3 and above all match)
expect(_nth_child_matches("-n+3", 3)).to_equal(true)
expect(_nth_child_matches("-n+3", 2)).to_equal(false)
```

</details>

#### matches a plain integer b

- matches a plain integer b
   - Expected: _nth_child_matches("3", 3) is true
   - Expected: _nth_child_matches("3", 4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches a plain integer b")
expect(_nth_child_matches("3", 3)).to_equal(true)
expect(_nth_child_matches("3", 4)).to_equal(false)
```

</details>

#### rejects a negative remainder (rem < 0) case for an+b with a<>0

- rejects a negative remainder (rem < 0) case for an+b with a<>0
   - Expected: _nth_child_matches("2n+5", 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a negative remainder (rem < 0) case for an+b with a<>0")
# 2n+5, pos=1 -> rem = 1-5 = -4 < 0 -> false
expect(_nth_child_matches("2n+5", 1)).to_equal(false)
```

</details>

### core.spl: _part_specificity

#### scores an id selector

- scores an id selector
   - Expected: _part_specificity("#foo", 0) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scores an id selector")
# #foo -> 100
expect(_part_specificity("#foo", 0)).to_equal(100)
```

</details>

#### scores an id.class compound selector

- scores an id.class compound selector
   - Expected: _part_specificity("#foo.bar", 0) equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scores an id.class compound selector")
# #foo.bar -> 110
expect(_part_specificity("#foo.bar", 0)).to_equal(110)
```

</details>

#### scores a single class selector

- scores a single class selector
   - Expected: _part_specificity(".bar", 0) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scores a single class selector")
expect(_part_specificity(".bar", 0)).to_equal(10)
```

</details>

#### scores a multi-class compound selector

- scores a multi-class compound selector
   - Expected: _part_specificity(".a.b.c", 0) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scores a multi-class compound selector")
# .a.b.c -> 3 classes * 10 = 30
expect(_part_specificity(".a.b.c", 0)).to_equal(30)
```

</details>

#### scores a bare tag selector

- scores a bare tag selector
   - Expected: _part_specificity("div", 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scores a bare tag selector")
expect(_part_specificity("div", 0)).to_equal(1)
```

</details>

#### scores the universal selector as zero

- scores the universal selector as zero
   - Expected: _part_specificity("*", 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scores the universal selector as zero")
expect(_part_specificity("*", 0)).to_equal(0)
```

</details>

#### scores a tag.class compound selector

- scores a tag.class compound selector
   - Expected: _part_specificity("div.a.b", 0) equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scores a tag.class compound selector")
# div.a.b -> 1 + 2*10 = 21
expect(_part_specificity("div.a.b", 0)).to_equal(21)
```

</details>

#### scores a tag#id compound selector

- scores a tag#id compound selector
   - Expected: _part_specificity("div#foo", 0) equals `101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scores a tag#id compound selector")
# div#foo -> 101 (no dot after hash)
expect(_part_specificity("div#foo", 0)).to_equal(101)
```

</details>

#### scores a tag#id.class compound selector

- scores a tag#id.class compound selector
   - Expected: _part_specificity("div#foo.bar", 0) equals `111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scores a tag#id.class compound selector")
# div#foo.bar -> 111
expect(_part_specificity("div#foo.bar", 0)).to_equal(111)
```

</details>

#### adds 10 per [attr] selector

- adds 10 per [attr] selector
   - Expected: _part_specificity("div[disabled]", 0) equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("adds 10 per [attr] selector")
# div[disabled] -> 1 + 10 = 11
expect(_part_specificity("div[disabled]", 0)).to_equal(11)
```

</details>

#### adds 10 per plain pseudo-class

- adds 10 per plain pseudo-class
   - Expected: _part_specificity("div:hover", 0) equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("adds 10 per plain pseudo-class")
# div:hover -> 1 + 10 = 11
expect(_part_specificity("div:hover", 0)).to_equal(11)
```

</details>

#### adds 10 for a :nth-child(...) functional pseudo-class

- adds 10 for a :nth-child(...) functional pseudo-class
   - Expected: _part_specificity("div:nth-child(2n+1)", 0) equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("adds 10 for a :nth-child(...) functional pseudo-class")
# div:nth-child(2n+1) -> 1 + 10 = 11
expect(_part_specificity("div:nth-child(2n+1)", 0)).to_equal(11)
```

</details>

#### returns the max-option specificity for :is()

- returns the max-option specificity for :is()
   - Expected: _part_specificity("div:is(#a, .b)", 0) equals `101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the max-option specificity for :is()")
# div:is(#a, .b) -> base 1 + max(100, 10) = 101
expect(_part_specificity("div:is(#a, .b)", 0)).to_equal(101)
```

</details>

#### rejects a malformed pseudo-class chain (bare colon with no name)

- rejects a malformed pseudo-class chain (bare colon with no name)
   - Expected: _part_specificity("div:", 0) equals `-1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a malformed pseudo-class chain (bare colon with no name)")
expect(_part_specificity("div:", 0)).to_equal(-1000000)
```

</details>

#### rejects an unknown functional pseudo-class name

- rejects an unknown functional pseudo-class name
   - Expected: _part_specificity("div:unknown-fn(x)", 0) equals `-1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an unknown functional pseudo-class name")
expect(_part_specificity("div:unknown-fn(x)", 0)).to_equal(-1000000)
```

</details>

#### rejects recursion beyond depth 32

- rejects recursion beyond depth 32
   - Expected: _part_specificity("div", 33) equals `-1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects recursion beyond depth 32")
expect(_part_specificity("div", 33)).to_equal(-1000000)
```

</details>

### core.spl: _group_specificity

#### sums per-part specificity, skipping empty and combinator parts

- sums per-part specificity, skipping empty and combinator parts
   - Expected: _group_specificity(parts, 0) equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sums per-part specificity, skipping empty and combinator parts")
# ["div", "", ">", ".a"] -> 1 + 0 + 0 + 10 = 11
val parts: [text] = ["div", "", ">", ".a"]
expect(_group_specificity(parts, 0)).to_equal(11)
```

</details>

#### propagates a malformed-part failure as -1000000

- propagates a malformed-part failure as -1000000
   - Expected: _group_specificity(parts, 0) equals `-1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates a malformed-part failure as -1000000")
val parts: [text] = ["div:"]
expect(_group_specificity(parts, 0)).to_equal(-1000000)
```

</details>

#### rejects recursion beyond depth 32

- rejects recursion beyond depth 32
   - Expected: _group_specificity(parts, 33) equals `-1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects recursion beyond depth 32")
val parts: [text] = ["div"]
expect(_group_specificity(parts, 33)).to_equal(-1000000)
```

</details>

### core.spl: _sort_candidates_by_specificity

#### returns the input unchanged for 0 or 1 candidates

- returns the input unchanged for 0 or 1 candidates
   - Expected: _sort_candidates_by_specificity(empty, specs).len() equals `0`
   - Expected: sorted_one[0] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the input unchanged for 0 or 1 candidates")
val empty: [i32] = []
val specs: [i32] = []
expect(_sort_candidates_by_specificity(empty, specs).len()).to_equal(0)
val one: [i32] = [5]
val one_specs: [i32] = [10, 20, 30, 40, 50, 60]
val sorted_one = _sort_candidates_by_specificity(one, one_specs)
expect(sorted_one[0]).to_equal(5)
```

</details>

#### sorts candidates ascending by specificity, tie-broken by index

- sorts candidates ascending by specificity, tie-broken by index
   - Expected: sorted[0] equals `1`
   - Expected: sorted[1] equals `3`
   - Expected: sorted[2] equals `0`
   - Expected: sorted[3] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sorts candidates ascending by specificity, tie-broken by index")
# candidate 0 spec=30, candidate 1 spec=10, candidate 2 spec=30, candidate 3 spec=20
val candidates: [i32] = [0, 1, 2, 3]
val specs: [i32] = [30, 10, 30, 20]
val sorted = _sort_candidates_by_specificity(candidates, specs)
# expected order: 1 (10), 3 (20), 0 (30, index 0<2), 2 (30, index 2)
expect(sorted[0]).to_equal(1)
expect(sorted[1]).to_equal(3)
expect(sorted[2]).to_equal(0)
expect(sorted[3]).to_equal(2)
```

</details>

#### sorts a longer list spanning multiple merge widths

- sorts a longer list spanning multiple merge widths
   - Expected: sorted[0] equals `7`
   - Expected: sorted[7] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sorts a longer list spanning multiple merge widths")
val candidates: [i32] = [0, 1, 2, 3, 4, 5, 6, 7]
val specs: [i32] = [80, 70, 60, 50, 40, 30, 20, 10]
val sorted = _sort_candidates_by_specificity(candidates, specs)
expect(sorted[0]).to_equal(7)
expect(sorted[7]).to_equal(0)
```

</details>

### core.spl: z-index and style-order merge sorts

#### returns empty for count <= 0

- returns empty for count <= 0
   - Expected: _sort_positive_z_indices(idx, 0, styles).len() equals `0`
   - Expected: _sort_style_order_indices(idx, 0, styles).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty for count <= 0")
val idx: [i32] = []
val styles: [gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer_style.Style] = []
expect(_sort_positive_z_indices(idx, 0, styles).len()).to_equal(0)
expect(_sort_style_order_indices(idx, 0, styles).len()).to_equal(0)
```

</details>

#### sorts indices ascending by z_index, tie-broken by index

- sorts indices ascending by z_index, tie-broken by index
   - Expected: sorted[0] equals `1`
   - Expected: sorted[1] equals `3`
   - Expected: sorted[2] equals `0`
   - Expected: sorted[3] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sorts indices ascending by z_index, tie-broken by index")
var s0 = renderer_default_style()
s0.z_index = 30
var s1 = renderer_default_style()
s1.z_index = 10
var s2 = renderer_default_style()
s2.z_index = 30
var s3 = renderer_default_style()
s3.z_index = 20
val styles = [s0, s1, s2, s3]
val idx: [i32] = [0, 1, 2, 3]
val sorted = _sort_positive_z_indices(idx, 4, styles)
expect(sorted[0]).to_equal(1)
expect(sorted[1]).to_equal(3)
expect(sorted[2]).to_equal(0)
expect(sorted[3]).to_equal(2)
```

</details>

#### sorts a longer z_index list spanning multiple merge widths

- sorts a longer z_index list spanning multiple merge widths
   - Expected: sorted[0] equals `7`
   - Expected: sorted[7] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sorts a longer z_index list spanning multiple merge widths")
var s0 = renderer_default_style()
s0.z_index = 8
var s1 = renderer_default_style()
s1.z_index = 7
var s2 = renderer_default_style()
s2.z_index = 6
var s3 = renderer_default_style()
s3.z_index = 5
var s4 = renderer_default_style()
s4.z_index = 4
var s5 = renderer_default_style()
s5.z_index = 3
var s6 = renderer_default_style()
s6.z_index = 2
var s7 = renderer_default_style()
s7.z_index = 1
val styles = [s0, s1, s2, s3, s4, s5, s6, s7]
val idx: [i32] = [0, 1, 2, 3, 4, 5, 6, 7]
val sorted = _sort_positive_z_indices(idx, 8, styles)
expect(sorted[0]).to_equal(7)
expect(sorted[7]).to_equal(0)
```

</details>

#### sorts indices ascending by CSS order, tie-broken by index

- sorts indices ascending by CSS order, tie-broken by index
   - Expected: sorted[0] equals `1`
   - Expected: sorted[1] equals `3`
   - Expected: sorted[2] equals `0`
   - Expected: sorted[3] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sorts indices ascending by CSS order, tie-broken by index")
var s0 = renderer_default_style()
s0.order = 3
var s1 = renderer_default_style()
s1.order = 1
var s2 = renderer_default_style()
s2.order = 3
var s3 = renderer_default_style()
s3.order = 2
val styles = [s0, s1, s2, s3]
val idx: [i32] = [0, 1, 2, 3]
val sorted = _sort_style_order_indices(idx, 4, styles)
expect(sorted[0]).to_equal(1)
expect(sorted[1]).to_equal(3)
expect(sorted[2]).to_equal(0)
expect(sorted[3]).to_equal(2)
```

</details>

#### sorts a longer order list spanning multiple merge widths

- sorts a longer order list spanning multiple merge widths
   - Expected: sorted[0] equals `7`
   - Expected: sorted[7] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sorts a longer order list spanning multiple merge widths")
var s0 = renderer_default_style()
s0.order = 8
var s1 = renderer_default_style()
s1.order = 7
var s2 = renderer_default_style()
s2.order = 6
var s3 = renderer_default_style()
s3.order = 5
var s4 = renderer_default_style()
s4.order = 4
var s5 = renderer_default_style()
s5.order = 3
var s6 = renderer_default_style()
s6.order = 2
var s7 = renderer_default_style()
s7.order = 1
val styles = [s0, s1, s2, s3, s4, s5, s6, s7]
val idx: [i32] = [0, 1, 2, 3, 4, 5, 6, 7]
val sorted = _sort_style_order_indices(idx, 8, styles)
expect(sorted[0]).to_equal(7)
expect(sorted[7]).to_equal(0)
```

</details>

### core.spl: rule-list merge helpers

#### merge_two_sorted_rule_lists_unique returns the non-empty side when one side is empty

- merge_two_sorted_rule_lists_unique returns the non-empty side when one side is empty
   - Expected: merged.len() equals `3`
   - Expected: merged2.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merge_two_sorted_rule_lists_unique returns the non-empty side when one side is empty")
val left: [i32] = []
val right: [i32] = [1, 2, 3]
val merged = merge_two_sorted_rule_lists_unique(left, right)
expect(merged.len()).to_equal(3)
val left2: [i32] = [4, 5]
val right2: [i32] = []
val merged2 = merge_two_sorted_rule_lists_unique(left2, right2)
expect(merged2.len()).to_equal(2)
```

</details>

#### merge_two_sorted_rule_lists_unique dedupes overlapping ids

- merge_two_sorted_rule_lists_unique dedupes overlapping ids
   - Expected: merged.len() equals `5`
   - Expected: merged[0] equals `1`
   - Expected: merged[1] equals `2`
   - Expected: merged[2] equals `3`
   - Expected: merged[3] equals `5`
   - Expected: merged[4] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merge_two_sorted_rule_lists_unique dedupes overlapping ids")
val left: [i32] = [1, 3, 5]
val right: [i32] = [2, 3, 5, 7]
val merged = merge_two_sorted_rule_lists_unique(left, right)
# union deduped: 1,2,3,5,7 -> 5 entries
expect(merged.len()).to_equal(5)
expect(merged[0]).to_equal(1)
expect(merged[1]).to_equal(2)
expect(merged[2]).to_equal(3)
expect(merged[3]).to_equal(5)
expect(merged[4]).to_equal(7)
```

</details>

#### merge_sorted_rule_lists_unique_count handles 0, 1, and 2-list cases

- merge_sorted_rule_lists_unique_count handles 0, 1, and 2-list cases
   - Expected: merge_sorted_rule_lists_unique_count(zero, 0).len() equals `0`
   - Expected: merge_sorted_rule_lists_unique_count(one, 1).len() equals `3`
   - Expected: merge_sorted_rule_lists_unique_count(two, 2).len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merge_sorted_rule_lists_unique_count handles 0, 1, and 2-list cases")
val zero: [[i32]] = []
expect(merge_sorted_rule_lists_unique_count(zero, 0).len()).to_equal(0)
val one_list: [i32] = [9, 9, 10]
val one: [[i32]] = [one_list]
expect(merge_sorted_rule_lists_unique_count(one, 1).len()).to_equal(3)
val a: [i32] = [1, 2]
val b: [i32] = [2, 3]
val two: [[i32]] = [a, b]
expect(merge_sorted_rule_lists_unique_count(two, 2).len()).to_equal(3)
```

</details>

#### merge_sorted_rule_lists_unique_count merges 3+ lists with dedupe (k-way path)

- merge_sorted_rule_lists_unique_count merges 3+ lists with dedupe (k-way path)
   - Expected: merged.len() equals `7`
   - Expected: merged[0] equals `1`
   - Expected: merged[3] equals `4`
   - Expected: merged[6] equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merge_sorted_rule_lists_unique_count merges 3+ lists with dedupe (k-way path)")
val a: [i32] = [1, 4, 7]
val b: [i32] = [2, 4, 8]
val c: [i32] = [3, 4, 9]
val lists: [[i32]] = [a, b, c]
val merged = merge_sorted_rule_lists_unique_count(lists, 3)
# union deduped: 1,2,3,4,7,8,9 -> 7 entries
expect(merged.len()).to_equal(7)
expect(merged[0]).to_equal(1)
expect(merged[3]).to_equal(4)
expect(merged[6]).to_equal(9)
```

</details>

#### rule_lists_from_counts allocates one list per requested count

- rule_lists_from_counts allocates one list per requested count
   - Expected: lists.len() equals `3`
   - Expected: lists[0].len() equals `2`
   - Expected: lists[1].len() equals `0`
   - Expected: lists[2].len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rule_lists_from_counts allocates one list per requested count")
val counts: [i32] = [2, 0, 3]
val lists = rule_lists_from_counts(counts)
expect(lists.len()).to_equal(3)
expect(lists[0].len()).to_equal(2)
expect(lists[1].len()).to_equal(0)
expect(lists[2].len()).to_equal(3)
```

</details>

### core.spl: selector bucket / small array helpers

#### selector_bucket_value_from_base extracts an id

- selector_bucket_value_from_base extracts an id
   - Expected: selector_bucket_value_from_base("#foo") equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selector_bucket_value_from_base extracts an id")
expect(selector_bucket_value_from_base("#foo")).to_equal("foo")
```

</details>

#### selector_bucket_value_from_base extracts a single class

- selector_bucket_value_from_base extracts a single class
   - Expected: selector_bucket_value_from_base(".bar") equals `bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selector_bucket_value_from_base extracts a single class")
expect(selector_bucket_value_from_base(".bar")).to_equal("bar")
```

</details>

#### selector_bucket_value_from_base extracts the id from a tag#id compound

- selector_bucket_value_from_base extracts the id from a tag#id compound
   - Expected: selector_bucket_value_from_base("div#foo") equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selector_bucket_value_from_base extracts the id from a tag#id compound")
expect(selector_bucket_value_from_base("div#foo")).to_equal("foo")
```

</details>

#### selector_bucket_value_from_base extracts the first class from a tag.class compound

- selector_bucket_value_from_base extracts the first class from a tag.class compound
   - Expected: selector_bucket_value_from_base("div.bar") equals `bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selector_bucket_value_from_base extracts the first class from a tag.class compound")
expect(selector_bucket_value_from_base("div.bar")).to_equal("bar")
```

</details>

#### selector_bucket_value_from_base returns empty for an empty base

- selector_bucket_value_from_base returns empty for an empty base
   - Expected: selector_bucket_value_from_base("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selector_bucket_value_from_base returns empty for an empty base")
expect(selector_bucket_value_from_base("")).to_equal("")
```

</details>

#### selector_bucket_value_from_base returns the bare tag when no id/class present

- selector_bucket_value_from_base returns the bare tag when no id/class present
   - Expected: selector_bucket_value_from_base("div") equals `div`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("selector_bucket_value_from_base returns the bare tag when no id/class present")
expect(selector_bucket_value_from_base("div")).to_equal("div")
```

</details>

#### text_seen_before finds a prior duplicate and reports absence otherwise

- text_seen_before finds a prior duplicate and reports absence otherwise
   - Expected: text_seen_before(values, 2, "a") is true
   - Expected: text_seen_before(values, 2, "c") is false
   - Expected: text_seen_before(values, 0, "a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("text_seen_before finds a prior duplicate and reports absence otherwise")
val values: [text] = ["a", "b", "a"]
expect(text_seen_before(values, 2, "a")).to_equal(true)
expect(text_seen_before(values, 2, "c")).to_equal(false)
expect(text_seen_before(values, 0, "a")).to_equal(false)
```

</details>

#### i32_list_prefix copies the first `count` elements

- i32_list_prefix copies the first `count` elements
   - Expected: prefix.len() equals `2`
   - Expected: prefix[0] equals `10`
   - Expected: prefix[1] equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("i32_list_prefix copies the first `count` elements")
val values: [i32] = [10, 20, 30, 40]
val prefix = i32_list_prefix(values, 2)
expect(prefix.len()).to_equal(2)
expect(prefix[0]).to_equal(10)
expect(prefix[1]).to_equal(20)
```

</details>

#### text_key_index_count finds a key's index and reports -1 when absent

- text_key_index_count finds a key's index and reports -1 when absent
   - Expected: text_key_index_count(keys, "y", 3) equals `1`
   - Expected: text_key_index_count(keys, "q", 3) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("text_key_index_count finds a key's index and reports -1 when absent")
val keys: [text] = ["x", "y", "z"]
expect(text_key_index_count(keys, "y", 3)).to_equal(1)
expect(text_key_index_count(keys, "q", 3)).to_equal(-1)
```

</details>

#### dict_key_index_count prefers the O(1) dict when the key is present

- dict_key_index_count prefers the O(1) dict when the key is present
   - Expected: dict_key_index_count(d, keys, "y", 3) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dict_key_index_count prefers the O(1) dict when the key is present")
var d: Dict<text, i32> = {}
d["y"] = 99
val keys: [text] = ["x", "y", "z"]
expect(dict_key_index_count(d, keys, "y", 3)).to_equal(99)
```

</details>

#### dict_key_index_count falls back to the linear scan when the key is absent from the dict

- dict_key_index_count falls back to the linear scan when the key is absent from the dict
   - Expected: dict_key_index_count(d, keys, "z", 3) equals `2`
   - Expected: dict_key_index_count(d, keys, "q", 3) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dict_key_index_count falls back to the linear scan when the key is absent from the dict")
val d: Dict<text, i32> = {}
val keys: [text] = ["x", "y", "z"]
expect(dict_key_index_count(d, keys, "z", 3)).to_equal(2)
expect(dict_key_index_count(d, keys, "q", 3)).to_equal(-1)
```

</details>

### core.spl: attribute/class matching helpers

#### unquote_css_attr_value strips matching double or single quotes

- unquote_css_attr_value strips matching double or single quotes
   - Expected: unquote_css_attr_value("\"foo\"") equals `foo`
   - Expected: unquote_css_attr_value("'foo'") equals `foo`
   - Expected: unquote_css_attr_value("foo") equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unquote_css_attr_value strips matching double or single quotes")
expect(unquote_css_attr_value("\"foo\"")).to_equal("foo")
expect(unquote_css_attr_value("'foo'")).to_equal("foo")
expect(unquote_css_attr_value("foo")).to_equal("foo")
```

</details>

#### attr_selector_matches evaluates the presence-only form

- attr_selector_matches evaluates the presence-only form
   - Expected: attr_selector_matches("disabled=\"disabled\"", "disabled") is true
   - Expected: attr_selector_matches("", "disabled") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("attr_selector_matches evaluates the presence-only form")
expect(attr_selector_matches("disabled=\"disabled\"", "disabled")).to_equal(true)
expect(attr_selector_matches("", "disabled")).to_equal(false)
```

</details>

#### attr_selector_matches evaluates the exact-match form

- attr_selector_matches evaluates the exact-match form
   - Expected: attr_selector_matches("type=\"text\"", "type=\"text\"") is true
   - Expected: attr_selector_matches("type=\"text\"", "type=\"radio\"") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("attr_selector_matches evaluates the exact-match form")
expect(attr_selector_matches("type=\"text\"", "type=\"text\"")).to_equal(true)
expect(attr_selector_matches("type=\"text\"", "type=\"radio\"")).to_equal(false)
```

</details>

#### attr_selector_matches evaluates the ^= prefix form

- attr_selector_matches evaluates the ^= prefix form
   - Expected: attr_selector_matches("href=\"https://example.com\"", "href^=\"https\"") is true
   - Expected: attr_selector_matches("href=\"https://example.com\"", "href^=\"ftp\"") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("attr_selector_matches evaluates the ^= prefix form")
expect(attr_selector_matches("href=\"https://example.com\"", "href^=\"https\"")).to_equal(true)
expect(attr_selector_matches("href=\"https://example.com\"", "href^=\"ftp\"")).to_equal(false)
```

</details>

#### attr_selector_matches evaluates the $= suffix form

- attr_selector_matches evaluates the $= suffix form
   - Expected: attr_selector_matches("href=\"file.png\"", "href$=\".png\"") is true
   - Expected: attr_selector_matches("href=\"file.png\"", "href$=\".jpg\"") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("attr_selector_matches evaluates the $= suffix form")
expect(attr_selector_matches("href=\"file.png\"", "href$=\".png\"")).to_equal(true)
expect(attr_selector_matches("href=\"file.png\"", "href$=\".jpg\"")).to_equal(false)
```

</details>

#### attr_selector_matches evaluates the case-insensitive ` i` flag

- attr_selector_matches evaluates the case-insensitive ` i` flag
   - Expected: attr_selector_matches("type=\"TEXT\"", "type=\"text\" i") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("attr_selector_matches evaluates the case-insensitive ` i` flag")
expect(attr_selector_matches("type=\"TEXT\"", "type=\"text\" i")).to_equal(true)
```

</details>

#### attr_selector_matches rejects an empty expression

- attr_selector_matches rejects an empty expression
   - Expected: attr_selector_matches("anything", "") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("attr_selector_matches rejects an empty expression")
expect(attr_selector_matches("anything", "")).to_equal(false)
```

</details>

#### class_words_has finds an exact class word

- class_words_has finds an exact class word
   - Expected: class_words_has(words, "b") is true
   - Expected: class_words_has(words, "z") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("class_words_has finds an exact class word")
val words: [text] = ["a", "b", "c"]
expect(class_words_has(words, "b")).to_equal(true)
expect(class_words_has(words, "z")).to_equal(false)
```

</details>

#### class_has_all requires every dotted class to be present

- class_has_all requires every dotted class to be present
   - Expected: class_has_all(words, ".a.b") is true
   - Expected: class_has_all(words, ".a.z") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("class_has_all requires every dotted class to be present")
val words: [text] = ["a", "b", "c"]
expect(class_has_all(words, ".a.b")).to_equal(true)
expect(class_has_all(words, ".a.z")).to_equal(false)
```

</details>

#### base_selector_matches matches by tag, class, and id

- base_selector_matches matches by tag, class, and id
   - Expected: base_selector_matches("div.a", "div", "a b", class_words, "foo") is true
   - Expected: base_selector_matches("#foo", "div", "a b", class_words, "foo") is true
   - Expected: base_selector_matches("span", "div", "a b", class_words, "foo") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("base_selector_matches matches by tag, class, and id")
val class_words: [text] = ["a", "b"]
expect(base_selector_matches("div.a", "div", "a b", class_words, "foo")).to_equal(true)
expect(base_selector_matches("#foo", "div", "a b", class_words, "foo")).to_equal(true)
expect(base_selector_matches("span", "div", "a b", class_words, "foo")).to_equal(false)
```

</details>

#### base_selector_matches matches the universal selector

- base_selector_matches matches the universal selector
   - Expected: base_selector_matches("*", "div", "", class_words, "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("base_selector_matches matches the universal selector")
val class_words: [text] = []
expect(base_selector_matches("*", "div", "", class_words, "")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 69 |
| Active scenarios | 69 |
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

- Canonical SPipe generation for source `730dfbe2a935a854bf73a2c31a49caf8691a5528c7623a6c6c19b6b5c993d48c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `730dfbe2a935a854bf73a2c31a49caf8691a5528c7623a6c6c19b6b5c993d48c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `730dfbe2a935a854bf73a2c31a49caf8691a5528c7623a6c6c19b6b5c993d48c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 68 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an empty/whitespace-only prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a comment-only preamble' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_pure_helpers_coverage_closure_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an at-rule preamble terminated by ;' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
