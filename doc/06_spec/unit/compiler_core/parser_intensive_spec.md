# Parser Intensive Specification

> Tests covering core.parser (intensive).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Intensive Specification

## Scenarios

### core.parser (intensive)

#### parses assignments and compound assignments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses assignments and compound assignments
   - Expected: expr_get_tag(a1) equals `EXPR_ASSIGN`
   - Expected: expr_get_tag(a2) equals `EXPR_COMPOUND_ASSIGN`
   - Expected: expr_get_int(a2) equals `TOK_PLUS`
   - Expected: expr_get_tag(a3) equals `EXPR_COMPOUND_ASSIGN`
   - Expected: expr_get_int(a3) equals `TOK_MINUS`
   - Expected: expr_get_tag(a4) equals `EXPR_COMPOUND_ASSIGN`
   - Expected: expr_get_int(a4) equals `TOK_STAR`
   - Expected: expr_get_tag(a5) equals `EXPR_COMPOUND_ASSIGN`
   - Expected: expr_get_int(a5) equals `TOK_SLASH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses assignments and compound assignments")
val a1 = parse_expr_src("x = 1")
expect(expr_get_tag(a1)).to_equal(EXPR_ASSIGN)
val a2 = parse_expr_src("x += 2")
expect(expr_get_tag(a2)).to_equal(EXPR_COMPOUND_ASSIGN)
expect(expr_get_int(a2)).to_equal(TOK_PLUS)
val a3 = parse_expr_src("x -= 2")
expect(expr_get_tag(a3)).to_equal(EXPR_COMPOUND_ASSIGN)
expect(expr_get_int(a3)).to_equal(TOK_MINUS)
val a4 = parse_expr_src("x *= 2")
expect(expr_get_tag(a4)).to_equal(EXPR_COMPOUND_ASSIGN)
expect(expr_get_int(a4)).to_equal(TOK_STAR)
val a5 = parse_expr_src("x /= 2")
expect(expr_get_tag(a5)).to_equal(EXPR_COMPOUND_ASSIGN)
expect(expr_get_int(a5)).to_equal(TOK_SLASH)
```

</details>

#### parses logical, comparison, and coalesce operators

- parses logical, comparison, and coalesce operators
   - Expected: expr_get_tag(e1) equals `EXPR_BINARY`
   - Expected: expr_get_tag(e2) equals `EXPR_BINARY`
   - Expected: expr_get_tag(e3) equals `EXPR_NULL_COALESCE`
   - Expected: expr_get_tag(e4) equals `EXPR_BINARY`
   - Expected: expr_get_tag(e5) equals `EXPR_BINARY`
   - Expected: expr_get_tag(e6) equals `EXPR_BINARY`
   - Expected: expr_get_tag(e7) equals `EXPR_BINARY`
   - Expected: expr_get_tag(e8) equals `EXPR_BINARY`
   - Expected: expr_get_tag(e9) equals `EXPR_BINARY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses logical, comparison, and coalesce operators")
val e1 = parse_expr_src("a and b")
expect(expr_get_tag(e1)).to_equal(EXPR_BINARY)
val e2 = parse_expr_src("a or b")
expect(expr_get_tag(e2)).to_equal(EXPR_BINARY)
val e3 = parse_expr_src("a ?? b")
expect(expr_get_tag(e3)).to_equal(EXPR_NULL_COALESCE)
val e4 = parse_expr_src("1 == 2")
expect(expr_get_tag(e4)).to_equal(EXPR_BINARY)
val e5 = parse_expr_src("1 != 2")
expect(expr_get_tag(e5)).to_equal(EXPR_BINARY)
val e6 = parse_expr_src("1 < 2")
expect(expr_get_tag(e6)).to_equal(EXPR_BINARY)
val e7 = parse_expr_src("1 > 2")
expect(expr_get_tag(e7)).to_equal(EXPR_BINARY)
val e8 = parse_expr_src("1 <= 2")
expect(expr_get_tag(e8)).to_equal(EXPR_BINARY)
val e9 = parse_expr_src("1 >= 2")
expect(expr_get_tag(e9)).to_equal(EXPR_BINARY)
```

</details>

#### parses unary forms

- parses unary forms
   - Expected: expr_get_tag(e1) equals `EXPR_UNARY`
   - Expected: expr_get_tag(e2) equals `EXPR_UNARY`
   - Expected: expr_get_tag(e3) equals `EXPR_UNARY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses unary forms")
val e1 = parse_expr_src("-x")
expect(expr_get_tag(e1)).to_equal(EXPR_UNARY)
val e2 = parse_expr_src("not x")
expect(expr_get_tag(e2)).to_equal(EXPR_UNARY)
val e3 = parse_expr_src("!x")
expect(expr_get_tag(e3)).to_equal(EXPR_UNARY)
```

</details>

#### parses postfix calls, fields, indexes, slices

- parses postfix calls, fields, indexes, slices
   - Expected: expr_get_tag(f1) equals `EXPR_FIELD_ACCESS`
   - Expected: expr_get_tag(f2) equals `EXPR_METHOD_CALL`
   - Expected: expr_get_tag(f3) equals `EXPR_CALL`
   - Expected: expr_get_tag(f4) equals `EXPR_INDEX`
   - Expected: expr_get_tag(f5) equals `EXPR_SLICE`
   - Expected: expr_get_tag(f6) equals `EXPR_SLICE`
   - Expected: expr_get_tag(f7) equals `EXPR_SLICE`
   - Expected: expr_get_tag(f8) equals `EXPR_FIELD_ACCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses postfix calls, fields, indexes, slices")
val f1 = parse_expr_src("obj.field")
expect(expr_get_tag(f1)).to_equal(EXPR_FIELD_ACCESS)
val f2 = parse_expr_src("obj.method(1, 2)")
expect(expr_get_tag(f2)).to_equal(EXPR_METHOD_CALL)
val f3 = parse_expr_src("f(1, 2)")
expect(expr_get_tag(f3)).to_equal(EXPR_CALL)
val f4 = parse_expr_src("arr[1]")
expect(expr_get_tag(f4)).to_equal(EXPR_INDEX)
val f5 = parse_expr_src("arr[:2]")
expect(expr_get_tag(f5)).to_equal(EXPR_SLICE)
val f6 = parse_expr_src("arr[1:]")
expect(expr_get_tag(f6)).to_equal(EXPR_SLICE)
val f7 = parse_expr_src("arr[1:2]")
expect(expr_get_tag(f7)).to_equal(EXPR_SLICE)
val f8 = parse_expr_src("obj?.field")
expect(expr_get_tag(f8)).to_equal(EXPR_FIELD_ACCESS)
```

</details>

#### parses strings with and without interpolation

- parses strings with and without interpolation
   - Expected: expr_get_tag(s1) equals `EXPR_STRING_LIT`
   - Expected: expr_get_tag(s2) equals `EXPR_STRING_LIT`
   - Expected: expr_get_tag(s3) equals `EXPR_STRING_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses strings with and without interpolation")
val s1 = parse_expr_src("\"hello\"")
expect(expr_get_tag(s1)).to_equal(EXPR_STRING_LIT)
# Braces doubled so this spec's own literals are not interpolated; the
# strings handed to the parser are still `"hello {name}!"` and the
# unterminated `"hello {name"`.
# CONTRACT (corrected 2026-08-21): the PARSER never stamps
# EXPR_INTERPOLATED_STRING (34). A string literal stays opaque at parse
# time -- tag EXPR_STRING_LIT (3) -- and its `{...}` regions are
# sub-parsed by a LATER pass (`core/string_interpolation_expand.spl`,
# and the flat->rich bridge's flat_bridge_build_string_interps), which
# deliberately relies on that broad StringLit representation. Tag 34 is
# produced only by desugar, which is exactly what the grammar registry
# (`spec/compiler_schema/registry/compiler.frontend.Grammar.sdn`)
# records. Asserting 34 here was asserting a production that has never
# existed in the parser. Bug: doc/08_tracking/bug/
# parser_intensive_interpolated_string_tag_never_stamped_by_parser_2026-08-21.md
val s2 = parse_expr_src("\"hello {{name}}!\"")
expect(expr_get_tag(s2)).to_equal(EXPR_STRING_LIT)
val s3 = parse_expr_src("\"hello {{name\"")
expect(expr_get_tag(s3)).to_equal(EXPR_STRING_LIT)
```

</details>

#### parses primary keywords and underscore

- parses primary keywords and underscore
   - Expected: expr_get_tag(r) equals `EXPR_RETURN`
   - Expected: expr_get_tag(b) equals `EXPR_BREAK`
   - Expected: expr_get_tag(c) equals `EXPR_CONTINUE`
   - Expected: expr_get_tag(p) equals `EXPR_PASS`
   - Expected: expr_get_tag(u) equals `EXPR_IDENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses primary keywords and underscore")
val r = parse_expr_src("return")
expect(expr_get_tag(r)).to_equal(EXPR_RETURN)
val b = parse_expr_src("break")
expect(expr_get_tag(b)).to_equal(EXPR_BREAK)
val c = parse_expr_src("continue")
expect(expr_get_tag(c)).to_equal(EXPR_CONTINUE)
val p = parse_expr_src("pass")
expect(expr_get_tag(p)).to_equal(EXPR_PASS)
val u = parse_expr_src("_")
expect(expr_get_tag(u)).to_equal(EXPR_IDENT)
```

</details>

#### parses full module declarations

- parses full module declarations
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses full module declarations")
val src = "use a.b.{c, d}\n" +
    "export c, d\n" +
    "extern fn ext(x: i64) -> i64\n" +
    "struct Point:\n" +
    "    x: i64\n" +
    "    y: i64\n" +
    "enum Color:\n" +
    "    Red\n" +
    "    Green\n" +
    "fn add(a: i64, b: i64) -> i64:\n" +
    "    return a + b\n" +
    "val x: i64 = 1\n" +
    "var y = 2\n" +
    "if x == 1:\n" +
    "    pass\n" +
    "elif x == 2:\n" +
    "    pass\n" +
    "else:\n" +
    "    pass\n" +
    "match x:\n" +
    "    case 1:\n" +
    "        pass\n"
val had_err = parse_module_src(src, "full.spl")
expect(had_err).to_equal(false)
```

</details>

#### reports errors for malformed match

- reports errors for malformed match
   - Expected: had_err is true
   - Expected: parser_error_count() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports errors for malformed match")
val bad = "match x:\n    nope 1\n"
val had_err = parse_module_src(bad, "bad_match.spl")
expect(had_err).to_equal(true)
expect(parser_error_count() > 0).to_equal(true)
```

</details>

#### parses hex literals

- parses hex literals
   - Expected: expr_get_tag(e) equals `EXPR_INT_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hex literals")
val e = parse_expr_src("0xFF")
expect(expr_get_tag(e)).to_equal(EXPR_INT_LIT)
```

</details>

#### parses binary literals

- parses binary literals
   - Expected: expr_get_tag(e) equals `EXPR_INT_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses binary literals")
val e = parse_expr_src("0b1010")
expect(expr_get_tag(e)).to_equal(EXPR_INT_LIT)
```

</details>

#### parses octal literals

- parses octal literals
   - Expected: expr_get_tag(e) equals `EXPR_INT_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses octal literals")
val e = parse_expr_src("0o755")
expect(expr_get_tag(e)).to_equal(EXPR_INT_LIT)
```

</details>

#### parses float literals

- parses float literals
   - Expected: expr_get_tag(e) equals `EXPR_FLOAT_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses float literals")
val e = parse_expr_src("3.14")
expect(expr_get_tag(e)).to_equal(EXPR_FLOAT_LIT)
```

</details>

#### parses nil literal

- parses nil literal
   - Expected: expr_get_tag(e) equals `EXPR_NIL_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses nil literal")
val e = parse_expr_src("nil")
expect(expr_get_tag(e)).to_equal(EXPR_NIL_LIT)
```

</details>

#### parses true literal

- parses true literal
   - Expected: expr_get_tag(e) equals `EXPR_BOOL_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses true literal")
val e = parse_expr_src("true")
expect(expr_get_tag(e)).to_equal(EXPR_BOOL_LIT)
```

</details>

#### parses false literal

- parses false literal
   - Expected: expr_get_tag(e) equals `EXPR_BOOL_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses false literal")
val e = parse_expr_src("false")
expect(expr_get_tag(e)).to_equal(EXPR_BOOL_LIT)
```

</details>

#### parses self keyword

- parses self keyword
   - Expected: expr_get_tag(e) equals `EXPR_IDENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses self keyword")
val e = parse_expr_src("self")
expect(expr_get_tag(e)).to_equal(EXPR_IDENT)
```

</details>

#### parses empty parentheses as unit

- parses empty parentheses as unit
   - Expected: expr_get_tag(e) equals `EXPR_UNIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty parentheses as unit")
val e = parse_expr_src("()")
expect(expr_get_tag(e)).to_equal(EXPR_UNIT)
```

</details>

#### parses empty array literal

- parses empty array literal
   - Expected: expr_get_tag(e) equals `EXPR_ARRAY_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty array literal")
val e = parse_expr_src("[]")
expect(expr_get_tag(e)).to_equal(EXPR_ARRAY_LIT)
```

</details>

#### parses array literal with trailing comma

- parses array literal with trailing comma
   - Expected: expr_get_tag(e) equals `EXPR_ARRAY_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses array literal with trailing comma")
val e = parse_expr_src("[1, 2,]")
expect(expr_get_tag(e)).to_equal(EXPR_ARRAY_LIT)
```

</details>

#### parses return without value

- parses return without value
   - Expected: expr_get_tag(e) equals `EXPR_RETURN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses return without value")
val e = parse_expr_src("return")
expect(expr_get_tag(e)).to_equal(EXPR_RETURN)
```

</details>

#### parses return with value

- parses return with value
   - Expected: expr_get_tag(e) equals `EXPR_RETURN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses return with value")
val e = parse_expr_src("return 42")
expect(expr_get_tag(e)).to_equal(EXPR_RETURN)
```

</details>

#### parses slice with start only

- parses slice with start only
   - Expected: expr_get_tag(e) equals `EXPR_SLICE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses slice with start only")
val e = parse_expr_src("arr[1:]")
expect(expr_get_tag(e)).to_equal(EXPR_SLICE)
```

</details>

#### parses slice with end only

- parses slice with end only
   - Expected: expr_get_tag(e) equals `EXPR_SLICE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses slice with end only")
val e = parse_expr_src("arr[:5]")
expect(expr_get_tag(e)).to_equal(EXPR_SLICE)
```

</details>

#### parses range exclusive

- parses range exclusive
   - Expected: expr_get_tag(e) equals `EXPR_RANGE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses range exclusive")
val e = parse_expr_src("0..10")
expect(expr_get_tag(e)).to_equal(EXPR_RANGE)
```

</details>

#### parses range inclusive

- parses range inclusive
   - Expected: expr_get_tag(e) equals `EXPR_RANGE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses range inclusive")
val e = parse_expr_src("0..=10")
expect(expr_get_tag(e)).to_equal(EXPR_RANGE)
```

</details>

#### parses power operator

- parses power operator
   - Expected: expr_get_tag(e) equals `EXPR_BINARY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses power operator")
val e = parse_expr_src("2 ** 3")
expect(expr_get_tag(e)).to_equal(EXPR_BINARY)
```

</details>

#### parses modulo operator

- parses modulo operator
   - Expected: expr_get_tag(e) equals `EXPR_BINARY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses modulo operator")
val e = parse_expr_src("7 % 3")
expect(expr_get_tag(e)).to_equal(EXPR_BINARY)
```

</details>

#### parses optional chaining

- parses optional chaining
   - Expected: expr_get_tag(e) equals `EXPR_FIELD_ACCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses optional chaining")
val e = parse_expr_src("obj?.field")
expect(expr_get_tag(e)).to_equal(EXPR_FIELD_ACCESS)
```

</details>

#### parses simple string without interpolation

- parses simple string without interpolation
   - Expected: expr_get_tag(e) equals `EXPR_STRING_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple string without interpolation")
val e = parse_expr_src("\"hello\"")
expect(expr_get_tag(e)).to_equal(EXPR_STRING_LIT)
```

</details>

#### parses array type annotation

- parses array type annotation
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses array type annotation")
val src = "fn f(arr: [i64]) -> [text]:\n    pass\n"
val had_err = parse_module_src(src, "arr_type.spl")
expect(had_err).to_equal(false)
```

</details>

#### parses Option type annotation

- parses Option type annotation
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Option type annotation")
val src = "fn f() -> Option<i64>:\n    return nil\n"
val had_err = parse_module_src(src, "opt_type.spl")
expect(had_err).to_equal(false)
```

</details>

#### parses postfix ? type annotation

- parses postfix ? type annotation
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses postfix ? type annotation")
val src = "fn f() -> i64?:\n    return nil\n"
val had_err = parse_module_src(src, "postfix_type.spl")
expect(had_err).to_equal(false)
```

</details>

#### parses text? option type

- parses text? option type
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses text? option type")
val src = "fn f() -> text?:\n    return nil\n"
val had_err = parse_module_src(src, "text_opt.spl")
expect(had_err).to_equal(false)
```

</details>

#### parses f64? option type

- parses f64? option type
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses f64? option type")
val src = "fn f() -> f64?:\n    return nil\n"
val had_err = parse_module_src(src, "f64_opt.spl")
expect(had_err).to_equal(false)
```

</details>

#### parses bool? option type

- parses bool? option type
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bool? option type")
val src = "fn f() -> bool?:\n    return nil\n"
val had_err = parse_module_src(src, "bool_opt.spl")
expect(had_err).to_equal(false)
```

</details>

#### parses Result type

- parses Result type
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Result type")
val src = "fn f() -> Result<i64>:\n    return nil\n"
val had_err = parse_module_src(src, "result_type.spl")
expect(had_err).to_equal(false)
```

</details>

<details>
<summary>Advanced: parses while loop</summary>

#### parses while loop

- parses while loop
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses while loop")
val src = "while x > 0:\n    x = x - 1\n"
val had_err = parse_module_src(src, "while.spl")
expect(had_err).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

- parses for loop
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses for loop")
val src = "for i in 0..10:\n    pass\n"
val had_err = parse_module_src(src, "for.spl")
expect(had_err).to_equal(false)
```

</details>


</details>

#### parses class declaration

- parses class declaration
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses class declaration")
val src = "class Point:\n    x: i64\n    y: i64\n"
val had_err = parse_module_src(src, "class.spl")
expect(had_err).to_equal(false)
```

</details>

#### parses impl block

- parses impl block
   - Expected: had_err is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses impl block")
val src = "impl Point:\n    fn get_x() -> i64:\n        return self.x\n"
val had_err = parse_module_src(src, "impl.spl")
expect(had_err).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/parser_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering core.parser (intensive).
- core.parser (intensive)

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5261074b988c32d9c4d4f6bb5934d71aa07c080ef968369efd1110cfdc6048c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5261074b988c32d9c4d4f6bb5934d71aa07c080ef968369efd1110cfdc6048c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5261074b988c32d9c4d4f6bb5934d71aa07c080ef968369efd1110cfdc6048c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler_core/parser_intensive_spec.spl
mirror: doc/06_spec/unit/compiler_core/parser_intensive_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/parser_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/parser_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/parser_intensive_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses assignments and compound assignments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/parser_intensive_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses logical, comparison, and coalesce operators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/parser_intensive_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses unary forms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
