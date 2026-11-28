# MC/DC coverage: module_tldr_sections_v1.spl

> For engineers who maintain the module-cache TLDR companion format and need to

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MC/DC coverage: module_tldr_sections_v1.spl

For engineers who maintain the module-cache TLDR companion format and need to

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/cache/coverage/module_tldr_sections_v1_mcdc_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

For engineers who maintain the module-cache TLDR companion format and need to
know which inputs the extractor and the strict reader accept or refuse.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/cache/coverage/module_tldr_sections_v1_mcdc_spec.spl`
   from the repository root. No fixture file and no host fact is read.
2. Measure coverage with
   `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<f> <seed> run <this spec>`
   (doc/07_guide/infra/testing/coverage.md); the target is every decision and
   condition seen both true and false.

## Lifecycle

Research: doc/01_research/local/dir_tldr_aspect.md
Plan: doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (AW-1)
Architecture: doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md
Design: doc/05_design/compiler/cache/aspect_tldr_async_trace.md (section 3)

## Decision inventory

Line numbers refer to `module_tldr_sections_v1.spl` at the commit this spec
was last measured against.

| Line | Decision | Conditions | Covering its |
|------|----------|------------|--------------|
| 27 | `pub ` prefix strip | c1 | pub and bare declarations |
| 30 | `not decl.starts_with("fn ")` | c1 | non-fn declaration is never generic |
| 34 | `lt > 0 and (paren < 0 or lt < paren)` | c1 lt, c2 no paren, c3 order | generic detection its |
| 38 | blank / space / tab / `#` line | c1..c4 | non-declaration line its |
| 41-42 | struct / class / enum / bitfield | c1..c4 | layout its |
| 44, 46 | trait, type | c1 | trait and type its |
| 48 | val / const | c1, c2 | const it |
| 50 | impl / extend | c1, c2 | impl it |
| 52 | generic fn | c1 | generic detection its |
| 59 | fn / me / static fn member | c1..c3 | impl header members it |
| 71 | paren scan loop | c1 | empty line, non-empty line |
| 73 | inside a string literal | c1 | "parentheses inside a string literal are not counted" |
| 74 | previous byte was a backslash | c1 | "an escaped quote does not end the literal" |
| 76 | byte is a backslash | c1 | same |
| 78 | byte is the closing quote | c1 | both string its |
| 80 | byte opens a string | c1 | both string its, plain line |
| 82 | byte is `#` outside a string | c1 | "a comment ends the count" |
| 84, 86 | `(` and `)` | c1 | "counts open minus close parentheses" |
| 93-94 | block end: bound, blank, space, tab | c1..c4 | block extent its |
| 103 | skip `@attribute` lines | c1 index>=0, c2 index<len, c3 `@` | attribute its |
| 105 | start out of range | c1, c2 | out-of-range its |
| 108 | head not a declaration | c1..c4 | block_at head its |
| 112 | trim trailing blanks | c1 last>start, c2 blank | trailing blank its |
| 116 | member loop | c1 | single and multi-line blocks |
| 117 | `kind != "impl"` | c1 | impl vs non-impl its |
| 119 | line is a member header | c1 | impl header members it |
| 125 | `depth > 0 and j + 1 <= last` | c1 open list, c2 lines left | "keeps the continuation lines of a multi-line parameter list", "an unclosed parameter list stops at the end of the block" |
| 137, 139 | scan loop, no-section line | c1 | sections_of_source its |
| 150 | `bar <= 0` | c1 | no bar, leading bar, normal |
| 158-165 | kind validity, 23 kinds | c1..c23 | one it per kind group, unknown kind |
| 172 | more records | c1 | none, one, many |
| 175 | missing newline | c1 | header without newline |
| 179 | no kind/count separator | c1 | empty head, leading space, no space |
| 183 | `not valid or count < 0` | c1, c2 | bad kind, bad count, good |
| 186 | count overruns text | c1 | overrun vs exact fit |
| 188 | terminator is not newline | c1 | wrong terminator |

Measured: 39 of 39 decisions and 60 of 60 conditions, each both true and
false (short-circuit aware). Exclusions: none.
Known defect, recorded and not asserted here: the record count is written in
characters and read in bytes
(doc/08_tracking/bug/tldr_section_framing_byte_char_unit_mix_2026-11-28.md).

## Scenarios

### TLDR sections: classifying a source line

#### ignores blank, indented, tab-indented and comment lines

- Classify an empty line, a space-indented line, a tab-indented line and a comment line
- Every one answers an empty kind, so nested or commented text never starts a section
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: module_tldr_section_kind_v1("") equals ``
   - Expected: module_tldr_section_kind_v1("  struct Hidden:") equals ``
   - Expected: module_tldr_section_kind_v1("\tstruct Hidden:") equals ``
   - Expected: module_tldr_section_kind_v1("# struct Hidden:") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Classify an empty line, a space-indented line, a tab-indented line and a comment line")
step("Every one answers an empty kind, so nested or commented text never starts a section")
expect(module_tldr_section_kind_v1("")).to_equal("")
expect(module_tldr_section_kind_v1("  struct Hidden:")).to_equal("")
expect(module_tldr_section_kind_v1("\tstruct Hidden:")).to_equal("")
expect(module_tldr_section_kind_v1("# struct Hidden:")).to_equal("")
```

</details>

#### classifies struct, class, enum and bitfield as layout, with or without pub

- Classify struct, class, enum and bitfield lines, bare and with the pub prefix
- All four declarations answer layout and the pub prefix is ignored
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: module_tldr_section_kind_v1("struct S:") equals `layout`
   - Expected: module_tldr_section_kind_v1("pub class C:") equals `layout`
   - Expected: module_tldr_section_kind_v1("enum E:") equals `layout`
   - Expected: module_tldr_section_kind_v1("pub bitfield B:") equals `layout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Classify struct, class, enum and bitfield lines, bare and with the pub prefix")
step("All four declarations answer layout and the pub prefix is ignored")
expect(module_tldr_section_kind_v1("struct S:")).to_equal("layout")
expect(module_tldr_section_kind_v1("pub class C:")).to_equal("layout")
expect(module_tldr_section_kind_v1("enum E:")).to_equal("layout")
expect(module_tldr_section_kind_v1("pub bitfield B:")).to_equal("layout")
```

</details>

#### classifies trait, type, const and impl declarations

- Classify trait, type, val, const, impl and extend lines
- Each declaration maps to its own kind; val and const share const, impl and extend share impl
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: module_tldr_section_kind_v1("trait T:") equals `trait`
   - Expected: module_tldr_section_kind_v1("pub type A = i64") equals `type`
   - Expected: module_tldr_section_kind_v1("val X: i64 = 1") equals `const`
   - Expected: module_tldr_section_kind_v1("const Y: i64 = 2") equals `const`
   - Expected: module_tldr_section_kind_v1("impl T for P:") equals `impl`
   - Expected: module_tldr_section_kind_v1("extend P:") equals `impl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Classify trait, type, val, const, impl and extend lines")
step("Each declaration maps to its own kind; val and const share const, impl and extend share impl")
expect(module_tldr_section_kind_v1("trait T:")).to_equal("trait")
expect(module_tldr_section_kind_v1("pub type A = i64")).to_equal("type")
expect(module_tldr_section_kind_v1("val X: i64 = 1")).to_equal("const")
expect(module_tldr_section_kind_v1("const Y: i64 = 2")).to_equal("const")
expect(module_tldr_section_kind_v1("impl T for P:")).to_equal("impl")
expect(module_tldr_section_kind_v1("extend P:")).to_equal("impl")
```

</details>

#### treats only fn declarations with type parameters before the parenthesis as generic

- Classify fn lines with type parameters, with none, and with a generic only inside the argument list
- Only type parameters before the parenthesis make a generic section; plain functions and argument generics answer empty
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: module_tldr_section_kind_v1("fn id<T>(x: T) -> T:") equals `generic`
   - Expected: module_tldr_section_kind_v1("pub fn id<T>(x: T) -> T:") equals `generic`
   - Expected: module_tldr_section_kind_v1("fn bare<T>") equals `generic`
   - Expected: module_tldr_section_kind_v1("fn plain(x: i64) -> i64:") equals ``
   - Expected: module_tldr_section_kind_v1("fn f(x: Box<T>) -> i64:") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Classify fn lines with type parameters, with none, and with a generic only inside the argument list")
step("Only type parameters before the parenthesis make a generic section; plain functions and argument generics answer empty")
expect(module_tldr_section_kind_v1("fn id<T>(x: T) -> T:")).to_equal("generic")
expect(module_tldr_section_kind_v1("pub fn id<T>(x: T) -> T:")).to_equal("generic")
expect(module_tldr_section_kind_v1("fn bare<T>")).to_equal("generic")
expect(module_tldr_section_kind_v1("fn plain(x: i64) -> i64:")).to_equal("")
expect(module_tldr_section_kind_v1("fn f(x: Box<T>) -> i64:")).to_equal("")
```

</details>

#### gives no section to a non-fn, non-declaration line

- Classify a use line, which is neither a declaration nor a function
- The answer is empty, so import lines never become sections
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: module_tldr_section_kind_v1("use std.spec") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Classify a use line, which is neither a declaration nor a function")
step("The answer is empty, so import lines never become sections")
expect(module_tldr_section_kind_v1("use std.spec")).to_equal("")
```

</details>

### TLDR sections: cutting a block out of the source lines

#### returns the declaration and its indented body

- Cut the block of a struct that is followed by another top-level declaration
- The struct and its field are returned and the next declaration is left out
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: module_tldr_block_at_v1(lines, 0, "layout") equals `struct A:\n    x: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut the block of a struct that is followed by another top-level declaration")
step("The struct and its field are returned and the next declaration is left out")
val lines = ["struct A:", "    x: i64", "val B = 1"]
expect(module_tldr_block_at_v1(lines, 0, "layout")).to_equal("struct A:\n    x: i64")
```

</details>

#### keeps tab-indented and interior blank lines but drops trailing blanks

- Cut a block holding a tab-indented line, an interior blank line and two trailing blank lines
- Interior blanks and tabs survive but the trailing blanks are trimmed
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: module_tldr_block_at_v1(lines, 0, "layout") equals `struct A:\n\tx: i64\n\n    y: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut a block holding a tab-indented line, an interior blank line and two trailing blank lines")
step("Interior blanks and tabs survive but the trailing blanks are trimmed")
val lines = ["struct A:", "\tx: i64", "", "    y: i64", "", ""]
expect(module_tldr_block_at_v1(lines, 0, "layout")).to_equal("struct A:\n\tx: i64\n\n    y: i64")
```

</details>

#### returns just the head when only blank lines follow

- Cut a one-line declaration followed only by blank lines
- Only the head line is returned, with no trailing newline
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: module_tldr_block_at_v1(lines, 0, "const") equals `val X = 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut a one-line declaration followed only by blank lines")
step("Only the head line is returned, with no trailing newline")
val lines = ["val X = 1", "", ""]
expect(module_tldr_block_at_v1(lines, 0, "const")).to_equal("val X = 1")
```

</details>

#### skips leading attribute lines to reach the declaration

- Cut a block starting at an index that points at two attribute lines
- The attributes are skipped and the block starts at the declaration
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: module_tldr_block_at_v1(lines, 0, "layout") equals `struct A:\n    x: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut a block starting at an index that points at two attribute lines")
step("The attributes are skipped and the block starts at the declaration")
val lines = ["@derive", "@other", "struct A:", "    x: i64"]
expect(module_tldr_block_at_v1(lines, 0, "layout")).to_equal("struct A:\n    x: i64")
```

</details>

#### returns empty for an index outside the lines

- Cut a block at index -1 and at an index past the last line
- Both answer empty rather than failing
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: module_tldr_block_at_v1(lines, -1, "layout") equals ``
   - Expected: module_tldr_block_at_v1(lines, 5, "layout") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut a block at index -1 and at an index past the last line")
step("Both answer empty rather than failing")
val lines = ["struct A:"]
expect(module_tldr_block_at_v1(lines, -1, "layout")).to_equal("")
expect(module_tldr_block_at_v1(lines, 5, "layout")).to_equal("")
```

</details>

#### returns empty when attributes run to the end of the lines

- Cut a block from lines that are only attributes
- Skipping attributes runs off the end and the answer is empty
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: module_tldr_block_at_v1(["@a", "@b"], 0, "layout") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut a block from lines that are only attributes")
step("Skipping attributes runs off the end and the answer is empty")
expect(module_tldr_block_at_v1(["@a", "@b"], 0, "layout")).to_equal("")
```

</details>

#### returns empty when the line is blank, indented, tab-indented or a comment

- Cut a block at a blank, an indented, a tab-indented and a comment line, then at a real declaration
- Only the real declaration yields a block; the other four answer empty
   - Text capture: after_step
   - Evidence: text output verified by 5 expected checks
   - Expected: module_tldr_block_at_v1(lines, 0, "const") equals ``
   - Expected: module_tldr_block_at_v1(lines, 1, "const") equals ``
   - Expected: module_tldr_block_at_v1(lines, 2, "const") equals ``
   - Expected: module_tldr_block_at_v1(lines, 3, "const") equals ``
   - Expected: module_tldr_block_at_v1(lines, 4, "const") equals `val Z = 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut a block at a blank, an indented, a tab-indented and a comment line, then at a real declaration")
step("Only the real declaration yields a block; the other four answer empty")
val lines = ["", "  x", "\tx", "# c", "val Z = 1"]
expect(module_tldr_block_at_v1(lines, 0, "const")).to_equal("")
expect(module_tldr_block_at_v1(lines, 1, "const")).to_equal("")
expect(module_tldr_block_at_v1(lines, 2, "const")).to_equal("")
expect(module_tldr_block_at_v1(lines, 3, "const")).to_equal("")
expect(module_tldr_block_at_v1(lines, 4, "const")).to_equal("val Z = 1")
```

</details>

#### keeps only member header lines of an impl block, bodies dropped

- Cut an impl block with fn, me, static fn and pub fn members, a body line and a val line
- Only the member header lines are kept, so importers see the surface without bodies
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: module_tldr_block_at_v1(lines, 0, "impl") equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut an impl block with fn, me, static fn and pub fn members, a body line and a val line")
step("Only the member header lines are kept, so importers see the surface without bodies")
val lines = ["impl T for P:", "    fn a() -> i64:", "        self.x", "    me b():", "    static fn c():", "    pub fn d():", "    val z = 1"]
val expected = "impl T for P:\n    fn a() -> i64:\n    me b():\n    static fn c():\n    pub fn d():"
expect(module_tldr_block_at_v1(lines, 0, "impl")).to_equal(expected)
```

</details>

#### keeps every line of a non-impl block

- Cut a trait block that has a method signature and a val line
- Every line of the trait is kept because only impl blocks are reduced to headers
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: module_tldr_block_at_v1(lines, 0, "trait") equals `trait T:\n    fn a() -> i64\n    val z = 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut a trait block that has a method signature and a val line")
step("Every line of the trait is kept because only impl blocks are reduced to headers")
val lines = ["trait T:", "    fn a() -> i64", "    val z = 1"]
expect(module_tldr_block_at_v1(lines, 0, "trait")).to_equal("trait T:\n    fn a() -> i64\n    val z = 1")
```

</details>

#### keeps the continuation lines of a multi-line parameter list

- Cut an impl block whose first member spreads its parameters over three lines, followed by a body line and a second member
- The header keeps all three lines up to the closing parenthesis, the body line is dropped and the next member follows
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: module_tldr_block_at_v1(lines, 0, "impl") equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut an impl block whose first member spreads its parameters over three lines, followed by a body line and a second member")
step("The header keeps all three lines up to the closing parenthesis, the body line is dropped and the next member follows")
val lines = ["impl T for P:", "    fn a(x: i64,", "            y: i64", "        ) -> i64:", "        x + y", "    me b():"]
val expected = "impl T for P:\n    fn a(x: i64,\n            y: i64\n        ) -> i64:\n    me b():"
expect(module_tldr_block_at_v1(lines, 0, "impl")).to_equal(expected)
```

</details>

#### an unclosed parameter list stops at the end of the block

- Cut an impl block whose only member opens a parameter list that never closes, first with one more line and then with none
- Every remaining line is kept and the cut ends with the block, never reading past it
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: module_tldr_block_at_v1(open_list, 0, "impl") equals `impl T for P:\n    fn a(x: i64,\n        y: i64`
   - Expected: module_tldr_block_at_v1(last_line, 0, "impl") equals `impl T for P:\n    fn a(x: i64,`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Cut an impl block whose only member opens a parameter list that never closes, first with one more line and then with none")
step("Every remaining line is kept and the cut ends with the block, never reading past it")
val open_list = ["impl T for P:", "    fn a(x: i64,", "        y: i64", "val NEXT = 1"]
expect(module_tldr_block_at_v1(open_list, 0, "impl")).to_equal("impl T for P:\n    fn a(x: i64,\n        y: i64")
val last_line = ["impl T for P:", "    fn a(x: i64,"]
expect(module_tldr_block_at_v1(last_line, 0, "impl")).to_equal("impl T for P:\n    fn a(x: i64,")
```

</details>

### TLDR sections: parenthesis balance of a line

#### counts open minus close parentheses

- Count an empty line, a closed list, an opening line, a closing line and a nested opening line
- A balanced or empty line is zero, an open list is positive, a closing line is negative
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: deltas equals `[0, 0, 1, -1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Count an empty line, a closed list, an opening line, a closing line and a nested opening line")
val deltas = [module_tldr_paren_delta_v1(""), module_tldr_paren_delta_v1("fn a(x: i64) -> i64:"),
    module_tldr_paren_delta_v1("fn a(x: i64,"), module_tldr_paren_delta_v1("    ) -> i64:"),
    module_tldr_paren_delta_v1("fn a(f: fn(i64,")]
step("A balanced or empty line is zero, an open list is positive, a closing line is negative")
expect(deltas).to_equal([0, 0, 1, -1, 2])
```

</details>

#### parentheses inside a string literal are not counted

- Count a line whose default argument is a string holding parentheses, closed and then left open after the literal
- Only the parentheses outside the literal count, so a literal cannot fake an open list
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: deltas equals `[0, 1, 0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Count a line whose default argument is a string holding parentheses, closed and then left open after the literal")
val deltas = [module_tldr_paren_delta_v1("fn a(s: text = \"((\") -> i64:"),
    module_tldr_paren_delta_v1("fn a(s: text = \")\","), module_tldr_paren_delta_v1("\"(((\"")]
step("Only the parentheses outside the literal count, so a literal cannot fake an open list")
expect(deltas).to_equal([0, 1, 0])
```

</details>

#### an escaped quote does not end the literal

- Count a line whose string holds an escaped quote and an escaped backslash before parentheses
- After an escaped quote the literal continues; after an escaped backslash the next quote closes it
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: [quote, backslash] equals `[1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Count a line whose string holds an escaped quote and an escaped backslash before parentheses")
val quote = module_tldr_paren_delta_v1("fn a(s: text = \"\\\"(\",")
val backslash = module_tldr_paren_delta_v1("fn a(s: text = \"\\\\\", (")
step("After an escaped quote the literal continues; after an escaped backslash the next quote closes it")
expect([quote, backslash]).to_equal([1, 2])
```

</details>

#### a comment ends the count

- Count a line with a parenthesis after `#`, and a line whose `#` sits inside a string
- Parentheses in a comment are ignored, but a `#` inside a literal is not a comment
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: deltas equals `[1, 0, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Count a line with a parenthesis after `#`, and a line whose `#` sits inside a string")
val deltas = [module_tldr_paren_delta_v1("fn a(x: i64,  # see (note"),
    module_tldr_paren_delta_v1("# (((("), module_tldr_paren_delta_v1("fn a(s: text = \"#\", (")]
step("Parentheses in a comment are ignored, but a `#` inside a literal is not a comment")
expect(deltas).to_equal([1, 0, 2])
```

</details>

### TLDR sections: extracting entries from source

#### returns no entries for source without declarations

- Extract sections from a comment and a plain function
- No entry is produced, because plain function bodies are deliberately excluded
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: module_tldr_sections_of_source_v1("# only a comment\nfn plain():\n    1\n").len() equals `0)  # oracle: count fixed by the literal fixture on the lines above`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Extract sections from a comment and a plain function")
step("No entry is produced, because plain function bodies are deliberately excluded")
expect(module_tldr_sections_of_source_v1("# only a comment\nfn plain():\n    1\n").len()).to_equal(0)  # oracle: count fixed by the literal fixture on the lines above
```

</details>

#### emits ordered kind|block entries and skips attributes and plain functions

- Extract sections from source with an attributed struct, a plain function and a generic function
- Entries come back in source order as kind|block, with the plain function left out
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: s.len() equals `2)  # oracle: count fixed by the literal fixture on the lines above`
   - Expected: s[0] equals `layout|struct A:\n    x: i64`
   - Expected: s[1] equals `generic|fn g<T>(x: T) -> T:\n    x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Extract sections from source with an attributed struct, a plain function and a generic function")
step("Entries come back in source order as kind|block, with the plain function left out")
val src = "@derive\nstruct A:\n    x: i64\n\nfn plain():\n    1\n\nfn g<T>(x: T) -> T:\n    x\n"
val s = module_tldr_sections_of_source_v1(src)
expect(s.len()).to_equal(2)  # oracle: count fixed by the literal fixture on the lines above
expect(s[0]).to_equal("layout|struct A:\n    x: i64")
expect(s[1]).to_equal("generic|fn g<T>(x: T) -> T:\n    x")
```

</details>

#### normalises CRLF line endings

- Extract sections from source written with CRLF line endings
- Both consts are found and no carriage return leaks into the text
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: s.len() equals `2)  # oracle: count fixed by the literal fixture on the lines above`
   - Expected: s[0] equals `const|val A = 1`
   - Expected: s[1] equals `const|val B = 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Extract sections from source written with CRLF line endings")
step("Both consts are found and no carriage return leaks into the text")
val s = module_tldr_sections_of_source_v1("val A = 1\r\nval B = 2\r\n")
expect(s.len()).to_equal(2)  # oracle: count fixed by the literal fixture on the lines above
expect(s[0]).to_equal("const|val A = 1")
expect(s[1]).to_equal("const|val B = 2")
```

</details>

### TLDR sections: rendering the wire form

#### renders nothing for no entries

- Render an empty entry list
- The wire form is the empty text
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: module_tldr_sections_render_v1([]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Render an empty entry list")
step("The wire form is the empty text")
expect(module_tldr_sections_render_v1([])).to_equal("")
```

</details>

#### frames each entry with its kind and body length and drops entries without a kind

- Render entries, one without a bar, one with a leading bar and two well-formed
- Only the well-formed entries are framed, each with its character count
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: w equals `section: layout 9\nstruct A:\nsection: const 5\nval X\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Render entries, one without a bar, one with a leading bar and two well-formed")
step("Only the well-formed entries are framed, each with its character count")
val w = module_tldr_sections_render_v1(["layout|struct A:", "nobar", "|orphan", "const|val X"])
expect(w).to_equal("section: layout 9\nstruct A:\nsection: const 5\nval X\n")
```

</details>

### TLDR sections: parsing the wire form

#### reads zero records from text that does not start a section

- Parse text that begins with something other than a section prefix
- No entry is read and nothing is consumed, so the caller sees where the sections end
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: entries.len() equals `0)  # oracle: count fixed by the literal fixture on the lines above`
   - Expected: consumed equals `0)  # oracle: count fixed by the literal fixture on the lines above`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse text that begins with something other than a section prefix")
step("No entry is read and nothing is consumed, so the caller sees where the sections end")
val (entries, consumed) = module_tldr_sections_parse_v1("sif:\n")
expect(entries.len()).to_equal(0)  # oracle: count fixed by the literal fixture on the lines above
expect(consumed).to_equal(0)  # oracle: count fixed by the literal fixture on the lines above
```

</details>

#### reads consecutive records and stops before trailing text

- Parse two records followed by trailing text
- Both entries are returned and the consumed count stops exactly before the trailing text
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: entries.len() equals `2)  # oracle: count fixed by the literal fixture on the lines above`
   - Expected: entries[0] equals `layout|ab`
   - Expected: entries[1] equals `trait|ab`
   - Expected: consumed equals `w.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse two records followed by trailing text")
step("Both entries are returned and the consumed count stops exactly before the trailing text")
val w = record("layout") + record("trait")
val (entries, consumed) = module_tldr_sections_parse_v1(w + "sif:\n")
expect(entries.len()).to_equal(2)  # oracle: count fixed by the literal fixture on the lines above
expect(entries[0]).to_equal("layout|ab")
expect(entries[1]).to_equal("trait|ab")
expect(consumed).to_equal(w.len())
```

</details>

#### accepts a record with an empty body

- Parse a record whose count is zero
- One entry with an empty body is returned and all 19 characters are consumed
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: entries.len() equals `1)  # oracle: count fixed by the literal fixture on the lines above`
   - Expected: entries[0] equals `layout|`
   - Expected: consumed equals `19)  # oracle: count fixed by the literal fixture on the lines above`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse a record whose count is zero")
step("One entry with an empty body is returned and all 19 characters are consumed")
val (entries, consumed) = module_tldr_sections_parse_v1("section: layout 0\n\n")
expect(entries.len()).to_equal(1)  # oracle: count fixed by the literal fixture on the lines above
expect(entries[0]).to_equal("layout|")
expect(consumed).to_equal(19)  # oracle: count fixed by the literal fixture on the lines above
```

</details>

#### rejects a header with no newline

- Parse a header that ends before any newline
- The reader answers -1 and returns no entry
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: entries.len() equals `0)  # oracle: count fixed by the literal fixture on the lines above`
   - Expected: consumed equals `-1)  # oracle: -1 is the documented malformed-record sentinel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse a header that ends before any newline")
step("The reader answers -1 and returns no entry")
val (entries, consumed) = module_tldr_sections_parse_v1("section: layout 2")
expect(entries.len()).to_equal(0)  # oracle: count fixed by the literal fixture on the lines above
expect(consumed).to_equal(-1)  # oracle: -1 is the documented malformed-record sentinel
```

</details>

#### rejects a header with no kind or no separator

- Parse headers with an empty head, a leading space and a kind with no count
- Each answers -1 because the kind and count cannot be separated
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: c1 equals `-1)  # oracle: -1 is the documented malformed-record sentinel`
   - Expected: c2 equals `-1)  # oracle: -1 is the documented malformed-record sentinel`
   - Expected: c3 equals `-1)  # oracle: -1 is the documented malformed-record sentinel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse headers with an empty head, a leading space and a kind with no count")
step("Each answers -1 because the kind and count cannot be separated")
val (_a, c1) = module_tldr_sections_parse_v1("section: \nab\n")
val (_b, c2) = module_tldr_sections_parse_v1("section:  2\nab\n")
val (_c, c3) = module_tldr_sections_parse_v1("section: layout\nab\n")
expect(c1).to_equal(-1)  # oracle: -1 is the documented malformed-record sentinel
expect(c2).to_equal(-1)  # oracle: -1 is the documented malformed-record sentinel
expect(c3).to_equal(-1)  # oracle: -1 is the documented malformed-record sentinel
```

</details>

#### rejects an unknown kind

- Parse a well-formed record whose kind is not in the valid set
- The reader answers -1 and returns no entry, so a spliced companion is refused
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: entries.len() equals `0)  # oracle: count fixed by the literal fixture on the lines above`
   - Expected: consumed equals `-1)  # oracle: -1 is the documented malformed-record sentinel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse a well-formed record whose kind is not in the valid set")
step("The reader answers -1 and returns no entry, so a spliced companion is refused")
val (entries, consumed) = module_tldr_sections_parse_v1(record("bogus"))
expect(entries.len()).to_equal(0)  # oracle: count fixed by the literal fixture on the lines above
expect(consumed).to_equal(-1)  # oracle: -1 is the documented malformed-record sentinel
```

</details>

#### rejects a non-numeric or negative count

- Parse records whose count is text and whose count is -1
- Both answer -1 because a count must be a non-negative number
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: c1 equals `-1)  # oracle: -1 is the documented malformed-record sentinel`
   - Expected: c2 equals `-1)  # oracle: -1 is the documented malformed-record sentinel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse records whose count is text and whose count is -1")
step("Both answer -1 because a count must be a non-negative number")
val (_a, c1) = module_tldr_sections_parse_v1("section: layout abc\nab\n")
val (_b, c2) = module_tldr_sections_parse_v1("section: layout -1\nab\n")
expect(c1).to_equal(-1)  # oracle: -1 is the documented malformed-record sentinel
expect(c2).to_equal(-1)  # oracle: -1 is the documented malformed-record sentinel
```

</details>

#### rejects a count that overruns the text

- Parse a record whose count is larger than the remaining text
- The reader answers -1, so a truncated companion never yields partial sections
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: consumed equals `-1)  # oracle: -1 is the documented malformed-record sentinel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse a record whose count is larger than the remaining text")
step("The reader answers -1, so a truncated companion never yields partial sections")
val (_p, consumed) = module_tldr_sections_parse_v1("section: layout 5\nab\n")
expect(consumed).to_equal(-1)  # oracle: -1 is the documented malformed-record sentinel
```

</details>

#### rejects a record whose terminator is not a newline

- Parse a record whose body is not followed by a newline
- The reader answers -1 because the record is not self-delimiting
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: consumed equals `-1)  # oracle: -1 is the documented malformed-record sentinel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse a record whose body is not followed by a newline")
step("The reader answers -1 because the record is not self-delimiting")
val (_p, consumed) = module_tldr_sections_parse_v1("section: layout 2\nabX")
expect(consumed).to_equal(-1)  # oracle: -1 is the documented malformed-record sentinel
```

</details>

### TLDR sections: the set of valid kinds

#### accepts the core declaration kinds

- Parse one record for each core declaration kind
- Each of the nine core kinds is accepted and read back with its body
   - Exec capture: after_step
   - Evidence: execution result verified by 9 expected checks
   - Expected: parsed_one("layout") equals `layout|ab`
   - Expected: parsed_one("trait") equals `trait|ab`
   - Expected: parsed_one("type") equals `type|ab`
   - Expected: parsed_one("const") equals `const|ab`
   - Expected: parsed_one("impl") equals `impl|ab`
   - Expected: parsed_one("impls") equals `impls|ab`
   - Expected: parsed_one("generic") equals `generic|ab`
   - Expected: parsed_one("inline") equals `inline|ab`
   - Expected: parsed_one("summary") equals `summary|ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse one record for each core declaration kind")
step("Each of the nine core kinds is accepted and read back with its body")
expect(parsed_one("layout")).to_equal("layout|ab")
expect(parsed_one("trait")).to_equal("trait|ab")
expect(parsed_one("type")).to_equal("type|ab")
expect(parsed_one("const")).to_equal("const|ab")
expect(parsed_one("impl")).to_equal("impl|ab")
expect(parsed_one("impls")).to_equal("impls|ab")
expect(parsed_one("generic")).to_equal("generic|ab")
expect(parsed_one("inline")).to_equal("inline|ab")
expect(parsed_one("summary")).to_equal("summary|ab")
```

</details>

#### accepts the macro kinds

- Parse one record for each macro kind
- All three macro kinds are accepted
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: parsed_one("macro-def") equals `macro-def|ab`
   - Expected: parsed_one("macro-use") equals `macro-use|ab`
   - Expected: parsed_one("macro-key") equals `macro-key|ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse one record for each macro kind")
step("All three macro kinds are accepted")
expect(parsed_one("macro-def")).to_equal("macro-def|ab")
expect(parsed_one("macro-use")).to_equal("macro-use|ab")
expect(parsed_one("macro-key")).to_equal("macro-key|ab")
```

</details>

#### accepts the generic template kinds

- Parse one record for each generic template kind
- All three generic template kinds are accepted
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: parsed_one("generic-template") equals `generic-template|ab`
   - Expected: parsed_one("generic-spec") equals `generic-spec|ab`
   - Expected: parsed_one("generic-spec-ctx") equals `generic-spec-ctx|ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse one record for each generic template kind")
step("All three generic template kinds are accepted")
expect(parsed_one("generic-template")).to_equal("generic-template|ab")
expect(parsed_one("generic-spec")).to_equal("generic-spec|ab")
expect(parsed_one("generic-spec-ctx")).to_equal("generic-spec-ctx|ab")
```

</details>

#### accepts the surface and export kinds

- Parse one record for each surface, export, declaration, fallback and use kind
- All six kinds are accepted
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: parsed_one("surface") equals `surface|ab`
   - Expected: parsed_one("surface-digest") equals `surface-digest|ab`
   - Expected: parsed_one("export") equals `export|ab`
   - Expected: parsed_one("decl") equals `decl|ab`
   - Expected: parsed_one("fallback") equals `fallback|ab`
   - Expected: parsed_one("use") equals `use|ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse one record for each surface, export, declaration, fallback and use kind")
step("All six kinds are accepted")
expect(parsed_one("surface")).to_equal("surface|ab")
expect(parsed_one("surface-digest")).to_equal("surface-digest|ab")
expect(parsed_one("export")).to_equal("export|ab")
expect(parsed_one("decl")).to_equal("decl|ab")
expect(parsed_one("fallback")).to_equal("fallback|ab")
expect(parsed_one("use")).to_equal("use|ab")
```

</details>

#### accepts the aspect-decl kind

- Parse a record of kind aspect-decl
- The aspect-decl record is accepted, so aspect declarations survive the round trip
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: parsed_one("aspect-decl") equals `aspect-decl|ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse a record of kind aspect-decl")
step("The aspect-decl record is accepted, so aspect declarations survive the round trip")
expect(parsed_one("aspect-decl")).to_equal("aspect-decl|ab")
```

</details>

#### accepts the join-point kind

- Parse a record of kind join-point
- The join-point record is accepted, as the last kind of the validity list
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: parsed_one("join-point") equals `join-point|ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-TLDR-AW1
step("Parse a record of kind join-point")
step("The join-point record is accepted, as the last kind of the validity list")
expect(parsed_one("join-point")).to_equal("join-point|ab")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-ASPECT-TLDR-AW1`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `267b4df3c3066e9dde912259db49608c4342801106313b9e53747b1a5c94657a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `267b4df3c3066e9dde912259db49608c4342801106313b9e53747b1a5c94657a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `267b4df3c3066e9dde912259db49608c4342801106313b9e53747b1a5c94657a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/cache/coverage/module_tldr_sections_v1_mcdc_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache/coverage/module_tldr_sections_v1_mcdc_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache/coverage/module_tldr_sections_v1_mcdc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache/coverage/module_tldr_sections_v1_mcdc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
