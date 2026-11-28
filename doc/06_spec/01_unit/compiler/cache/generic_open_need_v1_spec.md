# Generic open needs (`generic_open_need_v1`)

> Purpose: pin the behaviour of the leaf module that describes what instances a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 82 | 82 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic open needs (`generic_open_need_v1`)

Purpose: pin the behaviour of the leaf module that describes what instances a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Plan | doc/03_plan/language/type_system/no_any_inference_plan.md (rows S3-F0..F10, row S3-F1) |
| Design | doc/05_design/compiler/cache/generic_instance_tldr_trace.md (sections 3, 4, 5, 9, 14) |
| Research | doc/01_research/compiler/compile_speed/mono_instance_census_2026-10-19.md (instance census this stage serves) |
| Source | `test/01_unit/compiler/cache/generic_open_need_v1_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: pin the behaviour of the leaf module that describes what instances a
generic template body needs, as rows over the template's own binders: the row,
its canonical order, the identity digest that instance keys fold, the nested
frame codec, and the wire form of the write-once open-needs slot.

Audience: compiler-cache maintainers who change the generic TLDR sections, and
reviewers who must be sure that moving a call never rebuilds an instance while
adding a needed instance always does.

Scope: `src/compiler/00.common/cache_contract/generic_open_need_v1.spl` only.
The section that carries the slot is specified in `generic_template_section_v3_spec.spl`.

Assumptions: argument keys are opaque non-empty text here; a binder key looks
like `v<symbol>#<index>` but this module never parses it.

Limitations: the evidence is runs of this spec on the Rust-seed interpreter
(`simple-local-20261128f.exe`); no native-compiled run backs it.

Verification and troubleshooting: run `simple test` on this file and read the
`SPEC FILE VERDICT:` line. A failure naming an error text means a refusal rule
changed its wording; the wording is part of the contract because callers surface it.

**Research:** doc/01_research/compiler/compile_speed/mono_instance_census_2026-10-19.md (instance census this stage serves)
**Architecture:** doc/04_architecture/generic_rr_hir_variant_obj.md (generic template facets and instance objects)
**Plan:** doc/03_plan/language/type_system/no_any_inference_plan.md (rows S3-F0..F10, row S3-F1)
**Design:** doc/05_design/compiler/cache/generic_instance_tldr_trace.md (sections 3, 4, 5, 9, 14)

| Requirement | Plan acceptance sentence it serves |
|---|---|
| REQ-GENERIC-F1A-001 frames | a v2 reader misses; every codec refusal is a miss, not a guess |
| REQ-GENERIC-F1A-002 rows and order | editing a body so that it needs one more instance changes the decoded open needs |
| REQ-GENERIC-F1A-003 identity digest | a call that only moves keeps its keys; a new needed instance changes them |
| REQ-GENERIC-F1A-004 instance key | the keys of that template's instances change with its needs |
| REQ-GENERIC-F1A-005 slot wire | Absent and Filled-empty differ on the wire; decode is the strict inverse of encode |

## Scenarios

### open needs of a generic template (plan S3-F1, provider side)

#### Frame codec of open needs

#### writing frames

#### writes each value as its byte length, a colon and the value

- write two values as frames
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_frames_v1(["ab", "c"]) equals `2:ab1:c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GENERIC-F1A-001
step("write two values as frames")
expect(generic_need_frames_v1(["ab", "c"])).to_equal("2:ab1:c")
```

</details>

#### writes an empty value as a zero-length frame

- write one empty value
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_frames_v1([""]) equals `0:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("write one empty value")
expect(generic_need_frames_v1([""])).to_equal("0:")
```

</details>

#### counts UTF-8 bytes, not characters, for a non-ASCII value

- write one non-ASCII value
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_frames_v1(["箱"]) equals `3:箱`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("write one non-ASCII value")
# oracle: the character 箱 is three UTF-8 bytes
expect(generic_need_frames_v1(["箱"])).to_equal("3:箱")
```

</details>

#### writes no frames for no values

- write an empty value list
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_frames_v1([]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("write an empty value list")
expect(generic_need_frames_v1([])).to_equal("")
```

</details>

#### reading frames back

#### returns the original values, including empty and non-ASCII ones

- write the frames of ab, an empty value, 箱 and x:y, then read them back
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: back.is_ok() is true
   - Expected: back.unwrap() equals `values`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("write the frames of ab, an empty value, 箱 and x:y, then read them back")
val values = ["ab", "", "箱", "x:y"]
val back = generic_need_frames_read_v1(generic_need_frames_v1(values))
expect(back.is_ok()).to_equal(true)
expect(back.unwrap()).to_equal(values)
```

</details>

#### reads a nested frame list as one value and the inner list again

- write an inner list and wrap it as a single outer frame
   - Exec capture: after_step
- read the outer list, then the inner frame
   - Expected: outer_values.len() equals `2)   # oracle: the outer list holds the head and the inner list`
   - Expected: outer_values[1] equals `inner`
   - Expected: generic_need_frames_read_v1(outer_values[1]).unwrap() equals `["k1", "k2"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("write an inner list and wrap it as a single outer frame")
val inner = generic_need_frames_v1(["k1", "k2"])
val outer = generic_need_frames_v1(["head", inner])
step("read the outer list, then the inner frame")
val outer_values = generic_need_frames_read_v1(outer).unwrap()
expect(outer_values.len()).to_equal(2)   # oracle: the outer list holds the head and the inner list
expect(outer_values[1]).to_equal(inner)
expect(generic_need_frames_read_v1(outer_values[1]).unwrap()).to_equal(["k1", "k2"])
```

</details>

#### reads empty data as no values

- read the empty string as a frame list
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_need_frames_read_v1("").unwrap() equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the empty string as a frame list")
expect(generic_need_frames_read_v1("").unwrap()).to_equal([])
```

</details>

#### refuses a header with no colon

- read a frame header with no colon
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `frame header has no ':'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @manual: folded
step("read a frame header with no colon")
val r = generic_need_frames_read_v1("5")
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("frame header has no ':'")
```

</details>

#### refuses a non-digit length

- read the data x:a
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_frames_read_v1("x:a").unwrap_err() equals `frame length: decimal holds a non-digit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the data x:a")
expect(generic_need_frames_read_v1("x:a").unwrap_err()).to_equal("frame length: decimal holds a non-digit")
```

</details>

#### refuses an empty length

- read the data :a
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_frames_read_v1(":a").unwrap_err() equals `frame length: empty decimal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the data :a")
expect(generic_need_frames_read_v1(":a").unwrap_err()).to_equal("frame length: empty decimal")
```

</details>

#### refuses a length with a leading zero

- read the data 01:a
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_frames_read_v1("01:a").unwrap_err() equals `frame length: decimal has a leading zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the data 01:a")
expect(generic_need_frames_read_v1("01:a").unwrap_err()).to_equal("frame length: decimal has a leading zero")
```

</details>

#### refuses a frame that runs past the end

- read the data 5:ab
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_frames_read_v1("5:ab").unwrap_err() equals `frame runs past the end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the data 5:ab")
expect(generic_need_frames_read_v1("5:ab").unwrap_err()).to_equal("frame runs past the end")
```

</details>

#### Canonical decimals of a span

#### accepted spellings

#### accepts zero and the widest twelve-digit offset

- parse the offsets 0 and 999999999999
   - Expected: r.is_ok() is true
   - Expected: r.unwrap().start.value equals `0)   # oracle: "0" is the smallest canonical offset`
   - Expected: r.unwrap().end.value equals `999999999999)   # oracle: twelve nines is the widest spelling`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parse the offsets 0 and 999999999999")
# oracle: the module allows 12 digits, so twelve 9s is the largest spelling
val widest = "999999999999"
val r = generic_need_span_from_values_v1("0", widest)
expect(r.is_ok()).to_equal(true)
expect(r.unwrap().start.value).to_equal(0)   # oracle: "0" is the smallest canonical offset
expect(r.unwrap().end.value).to_equal(999999999999)   # oracle: twelve nines is the widest spelling
```

</details>

#### rejected spellings

#### refuses an empty offset

- parse an empty start with the end 1
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_span_from_values_v1("", "1").unwrap_err() equals `span start: empty decimal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parse an empty start with the end 1")
expect(generic_need_span_from_values_v1("", "1").unwrap_err()).to_equal("span start: empty decimal")
```

</details>

#### refuses a thirteen-digit offset as too long

- parse the end 1234567890123
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_span_from_values_v1("1", "1234567890123").unwrap_err() equals `span end: decimal too long`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parse the end 1234567890123")
# oracle: 13 digits is one more than the 12-digit width
expect(generic_need_span_from_values_v1("1", "1234567890123").unwrap_err()).to_equal("span end: decimal too long")
```

</details>

#### refuses a character just below the digits

- parse the start /
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_span_from_values_v1("/", "1").unwrap_err() equals `span start: decimal holds a non-digit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parse the start /")
# oracle: '/' is code 47, one below '0'
expect(generic_need_span_from_values_v1("/", "1").unwrap_err()).to_equal("span start: decimal holds a non-digit")
```

</details>

#### refuses a character just above the digits

- parse the end :
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_span_from_values_v1("1", ":").unwrap_err() equals `span end: decimal holds a non-digit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parse the end :")
# oracle: ':' is code 58, one above '9'
expect(generic_need_span_from_values_v1("1", ":").unwrap_err()).to_equal("span end: decimal holds a non-digit")
```

</details>

#### refuses a leading zero

- parse the start 01 with the end 2
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_span_from_values_v1("01", "2").unwrap_err() equals `span start: decimal has a leading zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parse the start 01 with the end 2")
expect(generic_need_span_from_values_v1("01", "2").unwrap_err()).to_equal("span start: decimal has a leading zero")
```

</details>

#### Canonical order of ranks

#### lists indices in ascending rank order

- order the ranks c, a, b
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_need_order_v1(["c", "a", "b"]) equals `[1, 2, 0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("order the ranks c, a, b")
expect(generic_need_order_v1(["c", "a", "b"])).to_equal([1, 2, 0])
```

</details>

#### keeps an already sorted list in place

- order the ranks a, b, c
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_need_order_v1(["a", "b", "c"]) equals `[0, 1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("order the ranks a, b, c")
expect(generic_need_order_v1(["a", "b", "c"])).to_equal([0, 1, 2])
```

</details>

#### reverses a reverse-sorted list

- order the ranks c, b, a
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_need_order_v1(["c", "b", "a"]) equals `[2, 1, 0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("order the ranks c, b, a")
expect(generic_need_order_v1(["c", "b", "a"])).to_equal([2, 1, 0])
```

</details>

#### drops a duplicate rank and keeps its first occurrence

- order the ranks b, a, b, c
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_need_order_v1(["b", "a", "b", "c"]) equals `[1, 0, 3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("order the ranks b, a, b, c")
expect(generic_need_order_v1(["b", "a", "b", "c"])).to_equal([1, 0, 3])
```

</details>

#### returns no indices for no ranks

- order an empty rank list
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_need_order_v1([]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("order an empty rank list")
expect(generic_need_order_v1([])).to_equal([])
```

</details>

#### Causes and spans of a need

#### the four known causes

#### accepts field, call, construct and bound-dispatch

- check each cause constant
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: generic_need_cause_check_v1(GENERIC_NEED_CAUSE_FIELD).unwrap() equals `field`
   - Expected: generic_need_cause_check_v1(GENERIC_NEED_CAUSE_CALL).unwrap() equals `call`
   - Expected: generic_need_cause_check_v1(GENERIC_NEED_CAUSE_CONSTRUCT).unwrap() equals `construct`
   - Expected: generic_need_cause_check_v1(GENERIC_NEED_CAUSE_BOUND_DISPATCH).unwrap() equals `bound-dispatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check each cause constant")
expect(generic_need_cause_check_v1(GENERIC_NEED_CAUSE_FIELD).unwrap()).to_equal("field")
expect(generic_need_cause_check_v1(GENERIC_NEED_CAUSE_CALL).unwrap()).to_equal("call")
expect(generic_need_cause_check_v1(GENERIC_NEED_CAUSE_CONSTRUCT).unwrap()).to_equal("construct")
expect(generic_need_cause_check_v1(GENERIC_NEED_CAUSE_BOUND_DISPATCH).unwrap()).to_equal("bound-dispatch")
```

</details>

#### refuses an unknown cause and names it

- check the cause guess
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_cause_check_v1("guess").unwrap_err() equals `unknown need cause 'guess'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check the cause guess")
expect(generic_need_cause_check_v1("guess").unwrap_err()).to_equal("unknown need cause 'guess'")
```

</details>

#### span ordering rule

#### accepts an empty span and a forward span

- check the spans 5..5 and 5..9
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: generic_need_span_check_v1(span(5, 5)).is_ok() is true
   - Expected: generic_need_span_check_v1(span(5, 9)).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check the spans 5..5 and 5..9")
expect(generic_need_span_check_v1(span(5, 5)).is_ok()).to_equal(true)
expect(generic_need_span_check_v1(span(5, 9)).is_ok()).to_equal(true)
```

</details>

#### refuses a span that starts before the source

- check the span -1..4
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_span_check_v1(span(-1, 4)).unwrap_err() equals `span starts before the source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check the span -1..4")
expect(generic_need_span_check_v1(span(-1, 4)).unwrap_err()).to_equal("span starts before the source")
```

</details>

#### refuses a span that ends before it starts

- check the span 9..4
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_span_check_v1(span(9, 4)).unwrap_err() equals `span ends before it starts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check the span 9..4")
expect(generic_need_span_check_v1(span(9, 4)).unwrap_err()).to_equal("span ends before it starts")
```

</details>

#### span wire values

#### spells a span as two canonical decimals

- write the wire values of the span 7..30
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_span_values_v1(span(7, 30)) equals `["7", "30"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("write the wire values of the span 7..30")
expect(generic_need_span_values_v1(span(7, 30))).to_equal(["7", "30"])
```

</details>

#### refuses a backward span read from the wire

- parse the start 9 with the end 4
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_span_from_values_v1("9", "4").unwrap_err() equals `span ends before it starts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parse the start 9 with the end 4")
expect(generic_need_span_from_values_v1("9", "4").unwrap_err()).to_equal("span ends before it starts")
```

</details>

#### ranks spans numerically, not alphabetically

- rank the spans 9..12 and 10..12
   - Expected: nine < ten is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("rank the spans 9..12 and 10..12")
val nine = generic_need_span_rank_v1(span(9, 12))
val ten = generic_need_span_rank_v1(span(10, 12))
expect(nine < ten).to_equal(true)
```

</details>

#### Rows of open needs

#### a well-formed row

#### is accepted unchanged

- check the row c<x> at 3..12 caused by call
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: r.is_ok() is true
   - Expected: r.unwrap().callee_template_id equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check the row c<x> at 3..12 caused by call")
val r = generic_open_need_check_v1(simple_need())
expect(r.is_ok()).to_equal(true)
expect(r.unwrap().callee_template_id).to_equal("c")
```

</details>

#### row rejection rules

#### refuses a need with no callee

- check a row whose callee is empty
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_open_need_check_v1(need("", ["x"], 1, 2, "call")).unwrap_err() equals `need names no callee template`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check a row whose callee is empty")
expect(generic_open_need_check_v1(need("", ["x"], 1, 2, "call")).unwrap_err()).to_equal("need names no callee template")
```

</details>

#### refuses an empty argument key

- check a row with the keys x and an empty key
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_open_need_check_v1(need("c", ["x", ""], 1, 2, "call")).unwrap_err() equals `need holds an empty argument key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check a row with the keys x and an empty key")
expect(generic_open_need_check_v1(need("c", ["x", ""], 1, 2, "call")).unwrap_err()).to_equal("need holds an empty argument key")
```

</details>

#### refuses an unknown cause

- check a row with the cause wish
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_open_need_check_v1(need("c", ["x"], 1, 2, "wish")).unwrap_err() equals `unknown need cause 'wish'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check a row with the cause wish")
expect(generic_open_need_check_v1(need("c", ["x"], 1, 2, "wish")).unwrap_err()).to_equal("unknown need cause 'wish'")
```

</details>

#### refuses a malformed span

- check a row spanning 5..2
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_open_need_check_v1(need("c", ["x"], 5, 2, "call")).unwrap_err() equals `span ends before it starts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check a row spanning 5..2")
expect(generic_open_need_check_v1(need("c", ["x"], 5, 2, "call")).unwrap_err()).to_equal("span ends before it starts")
```

</details>

#### accepts a need with no argument keys

- check a row with no argument keys
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_open_need_check_v1(need("c", [], 1, 2, "field")).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check a row with no argument keys")
expect(generic_open_need_check_v1(need("c", [], 1, 2, "field")).is_ok()).to_equal(true)
```

</details>

#### Canonical order of a row list

#### orders rows by callee first

- sort the rows b<x> and a<x>
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: callees_of(generic_open_needs_canonical_v1(rows).unwrap()) equals `["a", "b"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("sort the rows b<x> and a<x>")
# @req REQ-GENERIC-F1A-002
val rows = [need("b", ["x"], 1, 2, "call"), need("a", ["x"], 1, 2, "call")]
expect(callees_of(generic_open_needs_canonical_v1(rows).unwrap())).to_equal(["a", "b"])
```

</details>

#### orders rows of one callee by argument keys

- sort the rows c<y> and c<x>
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: sorted[0].arg_keys equals `["x"]`
   - Expected: sorted[1].arg_keys equals `["y"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("sort the rows c<y> and c<x>")
val rows = [need("c", ["y"], 1, 2, "call"), need("c", ["x"], 1, 2, "call")]
val sorted = generic_open_needs_canonical_v1(rows).unwrap()
expect(sorted[0].arg_keys).to_equal(["x"])
expect(sorted[1].arg_keys).to_equal(["y"])
```

</details>

#### orders rows with equal callee and keys by span numerically (offset 9 before offset 10)

- sort the rows c<x> at 10..11 and 9..11
   - Expected: starts_of(generic_open_needs_canonical_v1(rows).unwrap()) equals `[9, 10]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("sort the rows c<x> at 10..11 and 9..11")
val rows = [need("c", ["x"], 10, 11, "call"), need("c", ["x"], 9, 11, "call")]
expect(starts_of(generic_open_needs_canonical_v1(rows).unwrap())).to_equal([9, 10])
```

</details>

#### orders rows that differ only by cause by the cause text

- sort the rows c<x> caused by field and by call
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: causes_of(generic_open_needs_canonical_v1(rows).unwrap()) equals `["call", "field"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("sort the rows c<x> caused by field and by call")
val rows = [need("c", ["x"], 1, 2, "field"), need("c", ["x"], 1, 2, "call")]
expect(causes_of(generic_open_needs_canonical_v1(rows).unwrap())).to_equal(["call", "field"])
```

</details>

#### drops an exact duplicate row

- sort the same row given twice
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_open_needs_canonical_v1(rows).unwrap().len() equals `1)   # oracle: an exact duplicate collapses to one row`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("sort the same row given twice")
val rows = [simple_need(), simple_need()]
expect(generic_open_needs_canonical_v1(rows).unwrap().len()).to_equal(1)   # oracle: an exact duplicate collapses to one row
```

</details>

#### keeps rows that differ only by span

- sort the rows c<x> at 1..2 and 3..4
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_open_needs_canonical_v1(rows).unwrap().len() equals `2)   # oracle: rows that differ only by span are both kept`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("sort the rows c<x> at 1..2 and 3..4")
val rows = [need("c", ["x"], 1, 2, "call"), need("c", ["x"], 3, 4, "call")]
expect(generic_open_needs_canonical_v1(rows).unwrap().len()).to_equal(2)   # oracle: rows that differ only by span are both kept
```

</details>

#### fails the whole list when one row is malformed

- sort a valid row together with a row of empty callee
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `need names no callee template`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("sort a valid row together with a row of empty callee")
val rows = [simple_need(), need("", ["x"], 1, 2, "call")]
val r = generic_open_needs_canonical_v1(rows)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("need names no callee template")
```

</details>

#### returns an empty list for no rows

- sort an empty row list
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_open_needs_canonical_v1([]).unwrap().len() equals `0)   # oracle: no rows in, no rows out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("sort an empty row list")
expect(generic_open_needs_canonical_v1([]).unwrap().len()).to_equal(0)   # oracle: no rows in, no rows out
```

</details>

#### Identity digest of open needs

#### equals a sha256 over the label and the hand-framed identity

- digest the single row c<x> and hash the hand-framed text
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_open_needs_identity_digest_v1([simple_need()]) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("digest the single row c<x> and hash the hand-framed text")
# @req REQ-GENERIC-F1A-003
# oracle: identity of callee "c" with keys ["x"] is "1:c" + "3:1:x" (the key list "1:x" is
# three bytes); the label is 30 bytes; the identity frame is 8 bytes.
val expected = sha256_text("30:" + DIGEST_LABEL + "8:1:c3:1:x")
expect(generic_open_needs_identity_digest_v1([simple_need()])).to_equal(expected)
```

</details>

#### ignores where a call moved to

- digest the row c<x> at 3..12 and at 400..420
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: after equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("digest the row c<x> at 3..12 and at 400..420")
val before = generic_open_needs_identity_digest_v1([need("c", ["x"], 3, 12, "call")])
val after = generic_open_needs_identity_digest_v1([need("c", ["x"], 400, 420, "call")])
expect(after).to_equal(before)
```

</details>

#### ignores why the instance is needed

- digest the row c<x> caused by call and by construct
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: b equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("digest the row c<x> caused by call and by construct")
val a = generic_open_needs_identity_digest_v1([need("c", ["x"], 3, 12, "call")])
val b = generic_open_needs_identity_digest_v1([need("c", ["x"], 3, 12, "construct")])
expect(b).to_equal(a)
```

</details>

#### ignores the order of rows and repeated rows

- digest rows a and b in both orders and with repeats
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: generic_open_needs_identity_digest_v1([two, one]) equals `base`
   - Expected: generic_open_needs_identity_digest_v1([one, two, one, one]) equals `base`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("digest rows a and b in both orders and with repeats")
val one = need("a", ["x"], 1, 2, "call")
val two = need("b", ["y"], 5, 6, "field")
val base = generic_open_needs_identity_digest_v1([one, two])
expect(generic_open_needs_identity_digest_v1([two, one])).to_equal(base)
expect(generic_open_needs_identity_digest_v1([one, two, one, one])).to_equal(base)
```

</details>

#### changes when a callee changes

- digest the row c<x> and the row d<x>
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: b != a is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("digest the row c<x> and the row d<x>")
val a = generic_open_needs_identity_digest_v1([need("c", ["x"], 1, 2, "call")])
val b = generic_open_needs_identity_digest_v1([need("d", ["x"], 1, 2, "call")])
expect(b != a).to_equal(true)
```

</details>

#### changes when an argument key changes

- digest the row c<x> and the row c<y>
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: b != a is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("digest the row c<x> and the row c<y>")
val a = generic_open_needs_identity_digest_v1([need("c", ["x"], 1, 2, "call")])
val b = generic_open_needs_identity_digest_v1([need("c", ["y"], 1, 2, "call")])
expect(b != a).to_equal(true)
```

</details>

#### changes when a row is added

- digest the row c<x> alone and with c<z> added
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: b != a is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("digest the row c<x> alone and with c<z> added")
val a = generic_open_needs_identity_digest_v1([need("c", ["x"], 1, 2, "call")])
val b = generic_open_needs_identity_digest_v1([need("c", ["x"], 1, 2, "call"), need("c", ["z"], 8, 9, "call")])
expect(b != a).to_equal(true)
```

</details>

#### differs between no needs and one need

- digest an empty row list and a one-row list
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_open_needs_identity_digest_v1([]) != generic_open_needs_identity_digest_v1([simple_need()]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("digest an empty row list and a one-row list")
expect(generic_open_needs_identity_digest_v1([]) != generic_open_needs_identity_digest_v1([simple_need()])).to_equal(true)
```

</details>

#### Open-needs component of an instance key

#### equals a sha256 over the label, the concrete key and the needs digest

- build the key of ck and nd and hash the hand-framed text
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_instance_needs_key_v1("ck", "nd") equals `sha256_text("25:generic-instance-needs/v12:ck2:nd")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build the key of ck and nd and hash the hand-framed text")
# @req REQ-GENERIC-F1A-004
# oracle: label "generic-instance-needs/v1" is 25 bytes; "ck" is 2; "nd" is 2
expect(generic_instance_needs_key_v1("ck", "nd")).to_equal(sha256_text("25:generic-instance-needs/v12:ck2:nd"))
```

</details>

#### moves when the concrete instance changes

- build the keys of ck1 and ck2 over the needs digest nd
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_instance_needs_key_v1("ck1", "nd") != generic_instance_needs_key_v1("ck2", "nd") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build the keys of ck1 and ck2 over the needs digest nd")
expect(generic_instance_needs_key_v1("ck1", "nd") != generic_instance_needs_key_v1("ck2", "nd")).to_equal(true)
```

</details>

#### moves when the needs it was built against change

- build the keys of ck over the needs digests nd1 and nd2
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_instance_needs_key_v1("ck", "nd1") != generic_instance_needs_key_v1("ck", "nd2") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build the keys of ck over the needs digests nd1 and nd2")
expect(generic_instance_needs_key_v1("ck", "nd1") != generic_instance_needs_key_v1("ck", "nd2")).to_equal(true)
```

</details>

#### Wire form of the open-needs slot

#### complete literal wires

#### writes an absent slot as the single frame 'absent'

- encode the absent slot
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Absent).unwrap() equals `6:absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode the absent slot")
expect(generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Absent).unwrap()).to_equal("6:absent")
```

</details>

#### writes a filled slot with no rows as the single frame 'filled'

- encode the filled slot holding no rows
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Filled(rows: [])).unwrap() equals `6:filled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode the filled slot holding no rows")
expect(generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Filled(rows: [])).unwrap()).to_equal("6:filled")
```

</details>

#### writes one row as state, then one nested row frame

- encode the slot holding the row c<x> at 3..12 caused by call
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: wire equals `6:filled21:1:c1:32:124:call3:1:x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode the slot holding the row c<x> at 3..12 caused by call")
# @req REQ-GENERIC-F1A-005
# oracle: row blob = "1:c" "1:3" "2:12" "4:call" "3:1:x" = 21 bytes, so the slot is
# the 6-byte state frame followed by "21:" and that blob
val wire = generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Filled(rows: [simple_need()])).unwrap()
expect(wire).to_equal("6:filled21:1:c1:32:124:call3:1:x")
```

</details>

#### round trip

#### decodes what it encoded, with a non-ASCII callee and several keys

- encode the row 箱<k1, k2> at 4..8, decode it and encode it again
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: rows.len() equals `1)   # oracle: one row was written`
   - Expected: rows[0].callee_template_id equals `箱`
   - Expected: rows[0].arg_keys equals `["k1", "k2"]`
   - Expected: rows[0].span.end.value equals `8)   # oracle: the row was written with end offset 8`
   - Expected: generic_open_needs_slot_encode_v1(back).unwrap() equals `wire`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode the row 箱<k1, k2> at 4..8, decode it and encode it again")
val row = need("箱", ["k1", "k2"], 4, 8, "construct")
val wire = generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Filled(rows: [row])).unwrap()
val back = generic_open_needs_slot_decode_v1(wire).unwrap()
val rows = filled_rows(back)
expect(rows.len()).to_equal(1)   # oracle: one row was written
expect(rows[0].callee_template_id).to_equal("箱")
expect(rows[0].arg_keys).to_equal(["k1", "k2"])
expect(rows[0].span.end.value).to_equal(8)   # oracle: the row was written with end offset 8
expect(generic_open_needs_slot_encode_v1(back).unwrap()).to_equal(wire)
```

</details>

#### keeps an absent slot and a filled-empty slot apart

- encode both states
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: absent_wire != empty_wire is true
- decode both and read the state back
   - Expected: is_absent(absent_back) is true
   - Expected: is_absent(empty_back) is false
   - Expected: filled_rows(empty_back).len() equals `0)   # oracle: a filled-empty slot holds no rows`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode both states")
val absent_wire = generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Absent).unwrap()
val empty_wire = generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Filled(rows: [])).unwrap()
expect(absent_wire != empty_wire).to_equal(true)
step("decode both and read the state back")
val absent_back = generic_open_needs_slot_decode_v1(absent_wire).unwrap()
val empty_back = generic_open_needs_slot_decode_v1(empty_wire).unwrap()
expect(is_absent(absent_back)).to_equal(true)
expect(is_absent(empty_back)).to_equal(false)
expect(filled_rows(empty_back).len()).to_equal(0)   # oracle: a filled-empty slot holds no rows
```

</details>

#### writes the canonical order whatever order the rows arrive in

- encode the rows a and b in both orders
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: w2 equals `w1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode the rows a and b in both orders")
val a = need("a", ["x"], 1, 2, "call")
val b = need("b", ["x"], 1, 2, "call")
val w1 = generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Filled(rows: [a, b])).unwrap()
val w2 = generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Filled(rows: [b, a])).unwrap()
expect(w2).to_equal(w1)
```

</details>

#### encoder refusal

#### refuses to write a filled slot holding a malformed row

- encode a slot whose row has an empty argument key
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `need holds an empty argument key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode a slot whose row has an empty argument key")
val r = generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Filled(rows: [need("c", [""], 1, 2, "call")]))
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("need holds an empty argument key")
```

</details>

#### decoder refusal: framing and state

#### refuses broken framing

- decode the data 6:abs
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal("6:abs") equals `frame runs past the end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode the data 6:abs")
expect(slot_refusal("6:abs")).to_equal("frame runs past the end")
```

</details>

#### refuses a slot with no state

- decode the empty string as a slot
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal("") equals `open-needs slot has no state`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode the empty string as a slot")
expect(slot_refusal("")).to_equal("open-needs slot has no state")
```

</details>

#### refuses an absent slot that holds rows

- decode the frames absent and ab
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal("6:absent2:ab") equals `absent open-needs slot holds rows`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode the frames absent and ab")
expect(slot_refusal("6:absent2:ab")).to_equal("absent open-needs slot holds rows")
```

</details>

#### refuses an unknown state

- decode the frame later
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal("5:later") equals `unknown open-needs state 'later'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode the frame later")
expect(slot_refusal("5:later")).to_equal("unknown open-needs state 'later'")
```

</details>

#### decoder refusal: rows

#### refuses a row with the wrong number of frames

- decode filled with one row frame holding only 1:a
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal("6:filled3:1:a") equals `need row does not hold five frames`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode filled with one row frame holding only 1:a")
# oracle: a row blob must hold five frames; "1:a" holds one
expect(slot_refusal("6:filled3:1:a")).to_equal("need row does not hold five frames")
```

</details>

#### refuses a row whose inner framing is broken

- decode filled with a row frame ab
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal("6:filled2:ab") equals `frame header has no ':'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode filled with a row frame ab")
expect(slot_refusal("6:filled2:ab")).to_equal("frame header has no ':'")
```

</details>

#### refuses a row with a bad span

- decode a row spanning 3..2
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal("6:filled20:1:c1:31:24:call3:1:x") equals `span ends before it starts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a row spanning 3..2")
# row blob "1:c" "1:3" "1:2" "4:call" "3:1:x": end 2 is before start 3
expect(slot_refusal("6:filled20:1:c1:31:24:call3:1:x")).to_equal("span ends before it starts")
```

</details>

#### refuses a row with a non-canonical span decimal

- decode a row whose start is spelled 03
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal("6:filled21:1:c2:031:24:call3:1:x") equals `span start: decimal has a leading zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a row whose start is spelled 03")
# start spelled "03"
expect(slot_refusal("6:filled21:1:c2:031:24:call3:1:x")).to_equal("span start: decimal has a leading zero")
```

</details>

#### refuses a row whose argument keys are not valid frames

- decode a row whose key list is 5:ab
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal("6:filled22:1:c1:12:124:call4:5:ab") equals `frame runs past the end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a row whose key list is 5:ab")
# key list "5:ab" claims five bytes but holds two
expect(slot_refusal("6:filled22:1:c1:12:124:call4:5:ab")).to_equal("frame runs past the end")
```

</details>

#### refuses a row with an unknown cause

- decode a row with the cause wish
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal("6:filled21:1:c1:32:124:wish3:1:x") equals `unknown need cause 'wish'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a row with the cause wish")
# row blob "1:c" "1:3" "2:12" "4:wish" "3:1:x"
expect(slot_refusal("6:filled21:1:c1:32:124:wish3:1:x")).to_equal("unknown need cause 'wish'")
```

</details>

#### refuses rows that are not in canonical order

- decode the rows b then a
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal(wire) equals `open-needs slot is not in canonical form`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode the rows b then a")
# rows "b" then "a": a valid encoder would write "a" first
val b_row = generic_need_frames_v1(["b", "1", "2", "call", generic_need_frames_v1(["x"])])
val a_row = generic_need_frames_v1(["a", "1", "2", "call", generic_need_frames_v1(["x"])])
val wire = generic_need_frames_v1(["filled", b_row, a_row])
expect(slot_refusal(wire)).to_equal("open-needs slot is not in canonical form")
```

</details>

#### refuses a duplicate row

- decode the row a written twice
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: slot_refusal(wire) equals `open-needs slot is not in canonical form`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode the row a written twice")
val row = generic_need_frames_v1(["a", "1", "2", "call", generic_need_frames_v1(["x"])])
val wire = generic_need_frames_v1(["filled", row, row])
expect(slot_refusal(wire)).to_equal("open-needs slot is not in canonical form")
```

</details>

#### Span end bound of the wire form

#### accepts a span ending at the largest encodable offset

- check a span from 0 to 999999999999
   - Expected: generic_need_span_check_v1(span(0, LARGEST_ENCODABLE_OFFSET)).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check a span from 0 to 999999999999")
expect(generic_need_span_check_v1(span(0, LARGEST_ENCODABLE_OFFSET)).is_ok()).to_equal(true)
```

</details>

#### refuses a span ending one past the largest encodable offset

- check a span from 0 to 1000000000000
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `span ends past the largest encodable offset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check a span from 0 to 1000000000000")
val r = generic_need_span_check_v1(span(0, LARGEST_ENCODABLE_OFFSET + 1))
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("span ends past the largest encodable offset")
```

</details>

#### refuses such a row in the row check, in canonicalisation and in slot encoding

- take a row ending one past the largest offset and pass it to each entry point
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: generic_open_need_check_v1(row).unwrap_err() equals `span ends past the largest encodable offset`
   - Expected: generic_open_needs_canonical_v1([simple_need(), row]).unwrap_err() equals `span ends past the largest encodable offset`
   - Expected: encoded.unwrap_err() equals `span ends past the largest encodable offset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("take a row ending one past the largest offset and pass it to each entry point")
val row = need("c", ["x"], 1, LARGEST_ENCODABLE_OFFSET + 1, "call")
expect(generic_open_need_check_v1(row).unwrap_err()).to_equal("span ends past the largest encodable offset")
expect(generic_open_needs_canonical_v1([simple_need(), row]).unwrap_err()).to_equal("span ends past the largest encodable offset")
val encoded = generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Filled(rows: [row]))
expect(encoded.unwrap_err()).to_equal("span ends past the largest encodable offset")
```

</details>

#### round-trips a row ending at the largest encodable offset

- encode and decode a slot holding a row from 5 to 999999999999
   - Expected: back.len() equals `1)   # oracle: one row was written`
   - Expected: back[0].span.end.value equals `LARGEST_ENCODABLE_OFFSET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode and decode a slot holding a row from 5 to 999999999999")
val row = need("c", ["x"], 5, LARGEST_ENCODABLE_OFFSET, "call")
val wire = generic_open_needs_slot_encode_v1(GenericOpenNeedsSlotV1.Filled(rows: [row])).unwrap()
val back = filled_rows(generic_open_needs_slot_decode_v1(wire).unwrap())
expect(back.len()).to_equal(1)   # oracle: one row was written
expect(back[0].span.end.value).to_equal(LARGEST_ENCODABLE_OFFSET)
```

</details>

#### reaches a thirteen-digit end from the wire only as a too-long decimal

- read the end offset 1000000000000 from wire values
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: generic_need_span_from_values_v1("0", "1000000000000").unwrap_err() equals `span end: decimal too long`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the end offset 1000000000000 from wire values")
# The decimal rule fires first, so the span bound is reached only by typed values.
expect(generic_need_span_from_values_v1("0", "1000000000000").unwrap_err()).to_equal("span end: decimal too long")
```

</details>

#### Bytewise order of ranks

#### orders ranks by UTF-8 bytes: B, a, é, 한 (this pins bytewise order)

- order the ranks 한, a, B, é
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_need_order_v1(["한", "a", "B", "é"]) equals `[2, 1, 3, 0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("order the ranks 한, a, B, é")
# oracle: UTF-8 first bytes are B 0x42, a 0x61, é 0xC3, 한 0xED, so B, a, é, 한 are input indices 2, 1, 3, 0
expect(generic_need_order_v1(["한", "a", "B", "é"])).to_equal([2, 1, 3, 0])
```

</details>

#### puts an upper-case letter before its lower-case twin after a shared prefix (bytewise)

- order the ranks key-a, key-B, key-b, key-A
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_need_order_v1(["key-a", "key-B", "key-b", "key-A"]) equals `[3, 1, 0, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("order the ranks key-a, key-B, key-b, key-A")
# oracle: bytewise A 0x41 < B 0x42 < a 0x61 < b 0x62, so input indices 3, 1, 0, 2
expect(generic_need_order_v1(["key-a", "key-B", "key-b", "key-A"])).to_equal([3, 1, 0, 2])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/language/type_system/no_any_inference_plan.md (rows S3-F0..F10, row S3-F1)`
- **Design:** `doc/05_design/compiler/cache/generic_instance_tldr_trace.md (sections 3, 4, 5, 9, 14)`
- **Research:** `doc/01_research/compiler/compile_speed/mono_instance_census_2026-10-19.md (instance census this stage serves)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-GENERIC-F1A-001`
- `REQ-GENERIC-F1A-002`
- `REQ-GENERIC-F1A-003`
- `REQ-GENERIC-F1A-004`
- `REQ-GENERIC-F1A-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1b0cc5e08db17982bb5720e39a8384701ebb3b41261307c301e640fa1b44560c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b0cc5e08db17982bb5720e39a8384701ebb3b41261307c301e640fa1b44560c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b0cc5e08db17982bb5720e39a8384701ebb3b41261307c301e640fa1b44560c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **98/100**; effective score: **98/100**; blockers: **0**.

SSpec documentization score: 98/100
source: 01_unit/compiler/cache/generic_open_need_v1_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache/generic_open_need_v1_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache/generic_open_need_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
